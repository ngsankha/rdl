class RDL::Graph
attr_accessor :nodes, :edges

  # Create an enum for the type of the node
  EXPR_TYPE = {
    :entry => 0,
    :begin_main => 1,
    :rescue => 2,
    :retry => 3,
    :done => 4,
    :if_head => 5,
    :if_then => 6,
    :if_else => 7,
    :join => 8,
    :begin_secondary => 9, # includes all effects in the rescue block
    :begin_with_rescue => 10
  }

  EXPR_TYPE_TO_STR = {
    EXPR_TYPE[:entry] => "entry",
    EXPR_TYPE[:begin_main] => "begin_main",
    EXPR_TYPE[:rescue] => "rescue",
    EXPR_TYPE[:retry] => "retry",
    EXPR_TYPE[:done] => "done",
    EXPR_TYPE[:if_head] => "if_head",
    EXPR_TYPE[:if_then] => "if_then",
    EXPR_TYPE[:if_else] => "if_else",
    EXPR_TYPE[:join] => "join",
    EXPR_TYPE[:begin_secondary] => "begin_secondary",
    EXPR_TYPE[:begin_with_rescue] => "begin_with_rescue"
  }

  EXPR_TYPE_TO_STATE = {
    RDL::Graph::EXPR_TYPE[:begin_main]      => :Initial,
    RDL::Graph::EXPR_TYPE[:rescue]          => :Error,
    RDL::Graph::EXPR_TYPE[:done]            => :Done,
    RDL::Graph::EXPR_TYPE[:begin_secondary] => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:if_head]         => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:if_then]         => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:join]            => nil,     # not a state boundary
    RDL::Graph::EXPR_TYPE[:begin_with_rescue] => nil   # not a state boundary
  }

  def initialize
    @nodes = {}
    @edges = {}
    @stack = []
    @begin_visited_main = false
    @begin_visited_secondary = true
    @predicates = ""
    @pred_name = []
    @retryable_begin_scopes = []
    @verify = false
    @begin_effects = {}
    @rescue_effects = {}
    @monotonic_pop_nodes = []
    @counter = Hash.new # Expr type to count mapping
    @states = Set.new
    @retry_on_read = false
    @correct_retry = false
  end

  def add_node(node)
    @nodes[node] = node.expr_type
  end

  def join_nodes(from1, from2, to)
    add_edge(from1, to)
    add_edge(from2, to)
    push_to_stack(to)
  end

  def retry_on_read?
    @retry_on_read
  end

  def get_count(expr_type)
    @counter[expr_type] = 0 unless @counter[expr_type]
    @counter[expr_type] += 1
    @counter[expr_type]
  end

  def get_monotonic_pop_nodes
    @monotonic_pop_nodes
  end

  def remove_first_monotonic_pop_node
    @monotonic_pop_nodes.shift
  end

  def push_to_stack(bbl)
    @monotonic_pop_nodes = []
    @stack << bbl
  end

  def pop_from_stack
    @monotonic_pop_nodes.push(@stack.last)
    @stack.pop
  end

  def get_stack
    @stack
  end

  def peek_stack
    return nil if @stack.empty?
    if @stack.last.get_expr_type == EXPR_TYPE[:retry]
      @stack.pop
      return peek_stack
    end
    @stack.last
  end

  def add_edge(from, to)
    # raise "Invalid node" unless @nodes[to]
    @edges[from] = {} unless @edges[from]
    @edges[from][to] = true
  end

  def get_graph_node(type)
    @nodes.each { |n| return n[0] if n[1] == type }
    return
  end

  def get_stack_node(type)
    @stack.reverse.each { |n| return n if @nodes[n] == type }
    return nil
  end

  def add_to_scope(node)
    @retryable_begin_scopes.push(node)
  end

  def remove_from_scope
    @retryable_begin_scopes.pop
  end

  def get_retryable_begin_node
    return nil if @retryable_begin_scopes.empty?
    @retryable_begin_scopes.last
  end

  def visited_begin_main?
    @begin_visited_main
  end

  def set_begin_visited_main(val)
    @begin_visited_main = val
  end

  def visited_begin_secondary?
    @begin_visited_secondary
  end

  def set_begin_visited_secondary(val)
    @begin_visited_secondary = val
  end

  def verify?
    @verify
  end

  def set_verify(val)
    @verify = val
  end

  def to_s
    str = "CFG Nodes:\n"
    @nodes.each { |n| str += "#{n} :::::------>> #{EXPR_TYPE_TO_STR[n[1]]}\n\n" }
    str += "CFG Edges:\n"
    @edges.each_key { |from|
      @edges[from].each_key { |to|
        str += "#{from} -> #{to}\n"
      }
    }
    str
  end
  
  ### CFG to Dafny Predicate Generation Algorithm ###
  # 
  # Check if the node has_state?
  # If it does, get the state of the node, generate the predicate
  #  and at the end update the from_state variable, reset the effects
  #  
  # Generation of the predicates:
  # 1. Get the state of the node
  # 2. Get the previous state from the from_state variable
  # 3. Check the type of the effect and decrement the counter of that variable
  # 4. If the current_state is a Done state, increment the success counter, otherwise set it to 0
  # Example:
  # If there is a Read effect, decrement the read counter (current state is not Done hence success == 0):
  # && v.state == #{from_state}
  # && v'.state == #{current_state}
  # && v'.read == v.read - 1
  # && v'.write == v.write
  # && v'.success == v.success == 0
  # 
  # Addressing control flow divergences:
  # Check if the node has more than one edge going out -> control flow diverges 
  # If it does, visit each node till it reached a node with no outgoing edges or 
  # a node with a state or an already visited node (back edge) - add effects along the way
  # Note: if the node has a state, generate the predicate and reset the effects
  # 
  # Caution: Don't reset the effects blindly. Once we come back to where the control flow diverged, 
  # the effects should be reset to before the divergence
  # 
  # Back Edge Naive implementation:
  # Currently we use a hashset to check the number of times a node is visited
  # If a node is visited more than once, it is a back edge, we generate the predicate but don't
  # visit its neighbors
  #
  # Improved Back Edge implementation:
  # if we need to revisit nodes with different accumulated states or effects, 
  # we’d keep a more detailed visited structure, like marking (node, from_state, effect_signature) 
  # as visited rather than just (node). 
  # That way, we allow revisiting the same node if it arrives with a different set of relevant states or effects.
  # Otherwise, if the exact same combination of node and effect state reappears,
  # we skip it to avoid infinite recursion.
  # 
  #
  # Notes:     
  # && (v'.write > v'.read ==> v'.write - v'.read <= 1)
  # We can add the above clause if read and write check the same resource.
  # Need more though when to add this clause
  #
  # END
  
  
  def get_dafny_state(node)
    EXPR_TYPE_TO_STATE[node.expr_type]
  end

  def generate_predicate(from_state, to_state, effects, lastop, from_node, to_node)
    cur_lastop = lastop[1]
    prev_lastop = lastop[0]
    
    # op_name is cur_lastop if it is not nil, else it is prev_lastop
    op_name = cur_lastop ? cur_lastop : prev_lastop
    @pred_name.push("TransitionFrom#{from_state}#{from_node.get_count}To#{to_state}#{to_node.get_count}with#{op_name}")
    @states.add("#{from_state}#{from_node.get_count}")
    @states.add("#{to_state}#{to_node.get_count}")
    pred_str = "predicate TransitionFrom#{from_state}#{from_node.get_count}To#{to_state}#{to_node.get_count}with#{op_name} (v:Variables, v':Variables)\n"
    pred_str << "  requires Valid(v)\n{\n"
    pred_str << "  && v.state == #{from_state}#{from_node.get_count}\n"
    pred_str << "  && v'.state == #{to_state}#{to_node.get_count}\n"

    # TODO: Count should be based on the number of unique writes in a begin block
    # if len(effects) > 1, then count should be v.count - len(effects), else v.count - 1
    if effects.length > 1
      pred_str << "  && v'.count == v.count - #{effects.length}\n"
    else
      pred_str << "  && v'.count == v.count - 1\n"
    end

    if prev_lastop == nil 
      pred_str << "  && v.lastop != Write\n"
    end

    if cur_lastop == nil && prev_lastop != nil
      if prev_lastop == :read
        pred_str << "  && v.lastop == Read\n"
      elsif prev_lastop == :write
        pred_str << "  && v.lastop == Write\n"
      end
      if to_state == :Done
        pred_str << "  && v'.lastop == None\n"
      end
    end

    if cur_lastop == :read
      pred_str << "  && v'.lastop == Read\n"
    elsif cur_lastop == :write
      pred_str << "  && v'.lastop == Write\n"
    end

    if to_state == :Done
      pred_str << "  && v'.success == v.success + 1\n"
    else
      pred_str << "  && v'.success == v.success == 0\n"
    end

    pred_str << "}\n\n"
    @predicates << pred_str
    pred_str
  end

  def update_lastop(lastop, new_op)
    lastop[0] = lastop[1]
    lastop[1] = new_op
  end

  # Visited is a Hash : [from_node, to_node] => Set of effects

  def live_dfs(current_node, from_node, from_state = :Initial, visited = Hash.new, effects = {}, lastop = [nil, nil])
    # if visited[current_node]
    #   visited[current_node] += 1
    # else
    #   visited[current_node] = 1
    # end

    # puts "\n******Visiting #{current_node} with effects so far: #{effects}********\n\n"

    current_state = get_dafny_state(current_node)

    if (current_state && from_state != current_state) || (from_state == :Error && current_state)
      
      visited_key = [from_node, current_node]
      visited_val = effects

      if visited.include?(visited_key)
        # check if the effects are in the set
        # if not the same, then we need to visit the node again
        if visited[visited_key].include?(visited_val)
          return
        else
          visited[visited_key].add(visited_val)
        end
      else
        visited[visited_key] = Set.new
        visited[visited_key].add(visited_val)
      end
      
      puts "Generating predicate from #{from_state} to #{current_state} with effects so far: #{effects}"
      puts "\nFrom Node: #{from_node}, Current Node: #{current_node}\n"
      # Get the last effect from the effects hash
      cur_lastop = effects.values.last
      update_lastop(lastop, cur_lastop)

      puts "Lastop list: #{lastop}\n\n"

      if from_state == :Initial && current_state == :Error
        if @begin_effects.length > 0
          puts "Begin effects (should be empty): #{@begin_effects}\n"
          @begin_effects = {}
        end
        effects.each do |sym, effect|
          base = sym.base.name if sym.is_a?(RDL::Type::GenericType)
          param = sym.params[0].name if sym.is_a?(RDL::Type::GenericType)
          if base && param
            @begin_effects[param] = [base, sym]
          end
        end
        puts "Begin effects: #{@begin_effects}\n"
      end

      if from_state == :Error 
        if @rescue_effects.length > 0
          # puts "Rescue effects (should be empty): #{@rescue_effects}\n"
          # @rescue_effects = {}
        end
        effects.each do |sym, effect|
          base = sym.base.name if sym.is_a?(RDL::Type::GenericType)
          param = sym.params[0].name if sym.is_a?(RDL::Type::GenericType)
          if base && param
            @rescue_effects[param] = [base, sym]
          end
        end
        puts "Rescue effects: #{@rescue_effects}\n"
      end


      # retry on read logic
      if from_state == :Error && current_state == :Error
        # check if the retry is the same err node
        if from_node.get_count == current_node.get_count && lastop[1] == :read
          @retry_on_read = true
        end
      end
      if from_state == :Error && current_state == :Initial
        # check if from_node begin_main and to_node rescue with read effect exists in the visited hash
        # if it does, then we have a retry on read
        puts "Checking for retry on read\n"
        begin_node = get_graph_node(RDL::Graph::EXPR_TYPE[:begin_main])
        rescue_node = get_graph_node(RDL::Graph::EXPR_TYPE[:rescue])
        effect_set = visited[[begin_node, rescue_node]]
        puts "Effect set: #{effect_set}\n"
        if effect_set && effect_set.any? { |eff| eff.values.include?(:read) }
          @retry_on_read = true
        end
      end

      puts generate_predicate(from_state, current_state, effects, lastop, from_node, current_node)
      from_state = current_state
      from_node = current_node
      effects = {}
    end

    # return if visited[current_node] == 2

    cur_symbols = extract_effect_symbols(current_node.effects) # a hashset

    cur_symbols.each do |sym, effect|
      if !effects.key?(sym)
        effects[sym] = effect
      end
    end

    # new_effects = effects_so_far + extract_effect_symbols(current_node.effects)

    # puts "Visiting #{current_node} with new effects: #{new_effects}\n"
    
    if current_state == :Initial # since we can cycle back to the initial state
      lastop = [nil, nil]
    end

    neighbors = @edges[current_node] || {}
    neighbors.each_key do |next_node|
      live_dfs(next_node, from_node, from_state, visited, Marshal.load(Marshal.dump(effects)), lastop.dup)
    end
  end

  def extract_effect_symbols(effects_arr)
    # If it is a Union type, check the types array of the Union type and see if it is a VarType
    # To improve this, make a symbol_dict a key-value pair with the obj id as the value
    # and effect (fine-grained parametric) as the key (effect => obj_id)
    symbols = {}
    
    effects_arr = [effects_arr] unless effects_arr.is_a?(Array)
    effects_arr = effects_arr.flatten

    # puts "Effects Array: #{effects_arr}\n"

    effects_arr.each do |eff|
      if eff.is_a?(RDL::Type::VarType)
        if !symbols.key?(eff)
          case eff.name
          when :open
            symbols[eff] = :write
          when :close
            symbols[eff] = :read
          when :write
            symbols[eff] = :write
          end
        end
      end
      if eff.is_a?(RDL::Type::UnionType)
        eff.types.each do |type|
          if type.is_a?(RDL::Type::VarType)
            if !symbols.key?(type)
              case type.name
              when :open
                symbols[type] = :write
              when :close
                symbols[type] = :read
              when :write
                symbols[type] = :write
              end
            end
          end
        end
      end
      if eff.is_a?(RDL::Type::NominalType)
        if !symbols.key?(eff)
          case eff.name
          when "Write"
            symbols[eff] = :write
          when "Read"
            symbols[eff] = :read
          end
        end
      end
      # #<RDL::Type::GenericType:0x0000000109df6fd8 
      # @base=#<RDL::Type::NominalType:0x0000000109d1c608 @name="Write">, 
      # @params=[#<RDL::Type::NominalType:0x0000000109d1c270 @name="Issue">]>
      if eff.is_a?(RDL::Type::GenericType)
        if !symbols.key?(eff)
          case eff.base.name
          when "Write"
            symbols[eff] = :write
          when "Read"
            symbols[eff] = :read
          when "Idem"
            symbols[eff] = :read
          end
        end
      end
    end
    symbols
  end

  def compare_effects_begin_rescue
    # Compare if all the Writes in the Begin block have a corresponding Read in the Rescue block
    # Read the begin_effects hash and check if the value is a Write, find the corresponding key in the rescue
    # effects hash and check if it is a Read
    @begin_effects.each do |key, val|
      if val[0] == "Write"
        rescue_val = @rescue_effects[key]
        if rescue_val.nil? || rescue_val[0] != "Read"
          return false
        end
      end
    end
    return true
  end

  def to_dafny
    live_dfs(@nodes.keys.first, @nodes.keys.first)
    success = nil
    comparison = compare_effects_begin_rescue

    puts "\n-------States------"
    puts @states
    puts "-------States------\n"

    if !comparison
      success = false
      puts "Success: #{success}"
      # raise "Write in Begin block does not have a corresponding Read in Rescue block\n"
      raise "Write-Read mismatch/not found\n"
    end

    if !retry_on_read?
      success = false
      puts "Success: #{success}"
      # raise "No retry on read. Reads can fail if request does not succeed.\n"
      raise "No retry on read\n"
    end

    dafny_states = "datatype State = "
    @states.each do |state|
      dafny_states << "| #{state}"
    end
    
    dafny_types = "\ndatatype LastOp = None | Read | Write\n

datatype Variables = Variables(
  count:nat,
  success:nat,
  lastop:LastOp,
  state:State
)

predicate Init(v:Variables)
{
  && v.state == Initial1
  && v.count > 0
  && v.lastop == None
  && v.success == 0
}\n\n"

    dafny_step = "datatype Step = \n"
    @pred_name.each do |pred|
      dafny_step << "  | #{pred}Step()\n"
    end
    dafny_step << "\n"

    dafny_next_step = "predicate NextStep(v:Variables, v':Variables, step:Step)
  requires Valid(v)
{
  match step"
    @pred_name.each do |pred|
      dafny_next_step << "\n\t  case #{pred}Step() => #{pred}(v, v')"
    end
    dafny_next_step << "\n}\n\n"

    dafny_next = "predicate Next(v:Variables, v':Variables)
  requires Valid(v)
{
  exists step :: NextStep(v, v', step)
}\n\n"
    
    dafny_valid = "predicate Valid(v:Variables)"

    dafny_valid_temp = ""
    @states.each do |state|
      if state != "Done1"
        dafny_valid_temp << " || v.state == #{state}"  
      end
    end

    dafny_valid << "
{
    && ((#{dafny_valid_temp}) ==> (v.success == 0))
    && ((v.state == Done1) ==> (v.success == 1))
}\n\n"

    dafny_valid_transition = "predicate ValidTransition(v:Variables, v':Variables)
{
    && v'.success - v.success <= 1
    && v.count - v'.count == 1
    && (v.lastop == Write ==> v'.lastop != Write)
}\n\n"

    dafny_safety = "lemma SafetyProof()
  ensures forall v | Init(v) :: Valid(v)
  ensures forall v, v' | (Valid(v) && Next(v, v')) :: Valid(v') && (ValidTransition(v,v'))
{
}\n\n"

    dafny_liveness = "type Trace = nat -> Variables

ghost predicate IsTrace(trace: Trace)
{
    Init(trace(0)) &&
    forall i: nat :: (Valid(trace(i)) && Next(trace(i), trace(i+1)))
}

lemma SafetyProofTrace(trace: Trace)
    requires Init(trace(0))
{
    // Base case:
    assert Init(trace(0));
    assert Valid(trace(0));

    assert Next(trace(0), trace(1)) ==> Valid(trace(1)) && ValidTransition(trace(0), trace(1));
    // assert Valid(trace(1)) && Next(trace(1), trace(2)) ==> Valid(trace(2)) && ValidTransition(trace(1), trace(2));

    // Inductive step:
    forall i | i >= 0
      ensures (Valid(trace(i)) && Next(trace(i), trace(i+1))) ==> (Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1)))
    {
      if Valid(trace(i)) && Next(trace(i), trace(i+1)){
        assert trace(i).success <= 1;
        if trace(i+1).state == Done1 {
          assert trace(i+1).success == 1;
        }
      }
      // assert Valid(trace(i)) && Next(trace(i), trace(i+1)) ==> Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1));
      // if Valid(trace(i)) && Next(trace(i), trace(i+1)) && Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1)) {
      //     assert trace(i).count > trace(i+1).count;
      //     assert trace(i+1).success <= 1;
      // }
    }
}

// Assume that the network errors will eventually correct
ghost predicate FairNetwork(trace: Trace) 
{
    IsTrace(trace) &&
    forall n: nat :: HasDone(n, trace)
}

ghost predicate HasDone(n: nat, trace: Trace)
{
    exists n' :: n <= n' && trace(n').state == Done1 && trace(n').success == 1
}

lemma LivenessProof(trace: Trace, n: nat)
      returns (n': nat)
    requires IsTrace(trace) && FairNetwork(trace)
    requires Init(trace(n))
    requires forall i: nat :: i >= n ==> (Valid(trace(i)) && Next(trace(i), trace(i+1)))
    ensures n <= n' && trace(n').state == Done1 && trace(n').success == 1
{
      n' := n;
    while true
      invariant n <= n'
      invariant (Valid(trace(n)) && Next(trace(n), trace(n+1)))
      invariant Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) && Valid(trace(n'+1))
      decreases if Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && Valid(trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) then trace(n').count else 0
    {
      SafetyProofTrace(trace);
      var prev := trace(n').count;
      var prev_n := n';

      n' := n' + 1;

      assert trace(n').count < prev;

      if trace(n').state == Done1 {
        assert trace(n').success == 1;
        break;
      }
    }
    assert trace(n').state == Done1;
    assert trace(n').success == 1;
}\n\n"

    # Combine all the dafny code and write it to a file
    dafny_code = dafny_states + dafny_types + @predicates + dafny_step + dafny_next_step + dafny_next + dafny_valid + dafny_valid_transition + dafny_safety + dafny_liveness
    File.open("dafny_code.dfy", "w") { |f| f.write(dafny_code) }
    
    # Run the cli command dafny verify dafny_code.dfy
    success = system("dafny verify dafny_code.dfy")
    
    if !success
      puts "Success: #{success}"
      raise "Verification failed"
    end
    puts "Success: #{success}"
    
    # puts @predicates
    # puts dafny_code
    # puts "Dafny code written to dafny_code.dfy"

  end

end

class RDL::Graph::BasicBlock
  attr_accessor :effects, :expr_type, :counter

  def initialize(effects, expr_type = nil, counter)
    if effects.is_a? Array
      @effects = effects
    else
      @effects = [effects]
    end
    @expr_type = expr_type
    @counter = counter
  end

  def add_effect(effect)
    if effect.is_a? Array
      effect.each { |e| @effects << e }
    else
      @effects << effect
    end
  end

  def get_expr_type
    @expr_type
  end

  def get_count
    @counter
  end

  def to_s
    "Expr_type: #{RDL::Graph::EXPR_TYPE.key(@expr_type)} :: #{@counter}\n"
  end
end