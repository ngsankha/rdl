module RDL::Type
  # Abstract base class for all types. This class
  # should never be instantiated directly.

  class TypeError < StandardError; end

  class Type

    @@contract_cache = {}

    def to_contract
      c = @@contract_cache[self]
      return c if c

      slf = self # Bind self to slf since contracts are executed in scope of associated method
      c = RDL::Contract::FlatContract.new(to_s) { |obj|
        raise TypeError, "Expecting #{to_s}, got object of class #{RDL::Util.rdl_type_or_class(obj)}" unless slf.member?(obj)
        true
      }
      return (@@contract_cache[self] = c)  # assignment evaluates to c
    end

    def nil_type?
      is_a?(SingletonType) && @val.nil?
    end

    def var_type?
      is_a?(VarType)
    end

    def optional_var_type?
      is_a?(OptionalType) && @type.var_type?
    end
    
    def fht_var_type?
      is_a?(FiniteHashType) && @elts.keys.all? { |k| k.is_a?(Symbol) } && @elts.values.all? { |v| v.optional_var_type? || v.var_type? }
    end

    def kind_of_var_input?
      var_type? || optional_var_type? || fht_var_type?
    end

    # default behavior, override in appropriate subclasses
    def canonical; return self; end
    def optional?; return false; end
    def vararg?; return false; end

    # [+ other +] is a Type
    # [+ inst +] is a Hash<Symbol, Type> representing an instantiation
    # [+ ileft +] is a %bool
    # [+ deferred_constraints +] is an Array<[Type, Type]>. When provided, instead of applying
    # constraints to VarTypes, we simply defer them by putting them in this array.
    # [+ no_constraint +] is a %bool indicating whether or not we should add to tuple/FHT constraints
    # if inst is nil, returns self <= other
    # if inst is non-nil and ileft, returns inst(self) <= other, possibly mutating inst to make this true
    # if inst is non-nil and !ileft, returns self <= inst(other), again possibly mutating inst
    def self.leq(left, right, inst=nil, ileft=true, deferred_constraints=nil, no_constraint: false, ast: nil, propagate: false, new_cons: {})
      #propagate = false
      left = inst[left.name] if inst && ileft && left.is_a?(VarType) && !left.to_infer && inst[left.name]
      right = inst[right.name] if inst && !ileft && right.is_a?(VarType) && !right.to_infer && inst[right.name]
      left = left.type if left.is_a? DependentArgType
      right = right.type if right.is_a? DependentArgType
      left = left.type if left.is_a? NonNullType # ignore nullness!
      right = right.type if right.is_a? NonNullType
      left = left.canonical
      right = right.canonical

      # top and bottom
      return true if left.is_a? BotType
      return true if right.is_a? TopType

      # dynamic
      return true if left.is_a? DynamicType
      return true if right.is_a? DynamicType

      # type variables
      begin inst.merge!(left.name => right); return true end if inst && ileft && left.is_a?(VarType) && !left.to_infer
      begin inst.merge!(right.name => left); return true end if inst && !ileft && right.is_a?(VarType) && !right.to_infer
      if left.is_a?(VarType) && !left.to_infer && right.is_a?(VarType) && !right.to_infer
        return left.name == right.name
      elsif left.is_a?(VarType) && left.to_infer && right.is_a?(VarType) && right.to_infer
        if deferred_constraints.nil?
          left.add_ubound(right, ast, new_cons, propagate: propagate) unless (left.ubounds.any? { |t, loc| t == right } || left.equal?(right))
          right.add_lbound(left, ast, new_cons, propagate: propagate) unless (right.lbounds.any? { |t, loc| t == left } || right.equal?(left))
        else
          deferred_constraints << [left, right]
        end
        return true
      elsif left.is_a?(VarType) && left.to_infer
        if deferred_constraints.nil?
          left.add_ubound(right, ast, new_cons, propagate: propagate) unless (left.ubounds.any? { |t, loc| t == right } || left.equal?(right))
        else
          deferred_constraints << [left, right] 
        end
        return true
      elsif right.is_a?(VarType) && right.to_infer
        if deferred_constraints.nil?
          right.add_lbound(left, ast, new_cons, propagate: propagate) unless (right.lbounds.any? { |t, loc| t == left } || right.equal?(left))
        else
          deferred_constraints << [left, right]
        end          
        return true
      end

      # union
      return left.types.all? { |t| leq(t, right, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) } if left.is_a?(UnionType)
      if right.instance_of?(UnionType)
        right.types.each { |t|
          # return true at first match, updating inst accordingly to first succeessful match
          new_inst = inst.dup unless inst.nil?
          if leq(left, t, new_inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
            inst.update(new_inst) unless inst.nil?
            return true
          end
        }
        return false
      end

      # intersection
      return right.types.all? { |t| leq(left, t, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) } if right.instance_of?(IntersectionType)
      return left.types.any? { |t| leq(t, right, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) } if left.is_a?(IntersectionType)


      # nominal
      return left.klass.ancestors.member?(right.klass) if left.is_a?(NominalType) && right.is_a?(NominalType)
      if (left.is_a?(NominalType) || left.is_a?(TupleType) || left.is_a?(FiniteHashType) || left.is_a?(PreciseStringType)) && right.is_a?(StructuralType)
        case left
        when TupleType
          lklass = Array
          base_inst = { self: left }
        when FiniteHashType
          lklass = Hash
          base_inst = { self: left }
          # hack
          k_bind = left.promote.params[0].to_s == "k" ? RDL::Globals.types[:bot] : left.promote.params[0]
          v_bind = left.promote.params[1].to_s == "v" ? RDL::Globals.types[:bot] : left.promote.params[1]
          base_inst[:k] = k_bind
          base_inst[:v] = v_bind
        when PreciseStringType
          lklass = String
          base_inst = { self: left }
        else
          lklass = left.klass
          base_inst = { self: left }
        end

        right.methods.each_pair { |m, t|
          return false unless lklass.method_defined?(m) || RDL::Typecheck.lookup({}, lklass.to_s, m, nil, make_unknown: false)#RDL::Globals.info.get(lklass, m, :type) ## Added the second condition because Rails lazily defines some methods.
          types, _ = RDL::Typecheck.lookup({}, lklass.to_s, m, nil, make_unknown: false)#RDL::Globals.info.get(lklass, m, :type)
          if types
            #non_dep_types = RDL::Typecheck.filter_comp_types(types, false)
            #raise "Need non-dependent types for method #{m} of class #{lklass} in order to use a structural type." if non_dep_types.empty?
            return false unless types.any? { |tlm|
              blk_typ = tlm.block.is_a?(RDL::Type::MethodType) ? tlm.block.args + [tlm.block.ret] : [tlm.block]
              if (tlm.args + blk_typ + [tlm.ret]).any? { |t| t.is_a? ComputedType }
                ## In this case, need to actually evaluate the ComputedType.
                ## Going to do this using the receiver `left` and the args from `t`
                ## If subtyping holds for this, then we know `left` does indeed have a method of the relevant type.
                computed_tlm = RDL::Typecheck.compute_types(tlm, lklass, left, t.args)
                leq(computed_tlm.instantiate(base_inst), t, nil, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
              else
              leq(tlm.instantiate(base_inst), t, nil, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) 
              # inst above is nil because the method types inside the class and
              # inside the structural type have an implicit quantifier on them. So
              # even if we're allowed to instantiate type variables we can't do that
              # inside those types
              end
            }
          end
        }
        return true
      end

      # singleton
      return left.val == right.val if left.is_a?(SingletonType) && right.is_a?(SingletonType)
      return true if left.is_a?(SingletonType) && left.val.nil? # right cannot be a SingletonType due to above conditional
      return leq(left.nominal, right, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) if left.is_a?(SingletonType) # fall through case---use nominal type for reasoning

      # generic
      if left.is_a?(GenericType) && right.is_a?(GenericType)
        formals, variance, _ = RDL::Globals.type_params[left.base.name]
        # do check here to avoid hiding errors if generic type written
        # with wrong number of parameters but never checked against
        # instantiated instances
        raise TypeError, "No type parameters defined for #{left.base.name}" unless formals
        return false unless left.base == right.base
        return variance.zip(left.params, right.params).all? { |v, tl, tr|
          case v
          when :+
            leq(tl, tr, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
          when :-
            leq(tr, tl, inst, !ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
          when :~
            #puts "About to check with #{tl}, #{tr}, and #{ileft} AND #{inst}"
            leq(tl, tr, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) && leq(tr, tl, inst, !ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
          else
            raise RuntimeError, "Unexpected variance #{v}" # shouldn't happen
          end
        }
      end
      if left.is_a?(GenericType) && right.is_a?(StructuralType)
        # similar to logic above for leq(NominalType, StructuralType, ...)
        formals, variance, _ = RDL::Globals.type_params[left.base.name]
        raise TypeError, "No type parameters defined for #{left.base.name}" unless formals
        base_inst = Hash[*formals.zip(left.params).flatten] # instantiation for methods in base's class
        klass = left.base.klass
        right.methods.each_pair { |meth, t|
          return false unless klass.method_defined?(meth) || RDL::Typecheck.lookup({}, klass.to_s, meth, nil, make_unknown: false)#RDL::Globals.info.get(klass, meth, :type) ## Added the second condition because Rails lazily defines some methods.
          types, _ = RDL::Typecheck.lookup({}, klass.to_s, meth, {}, make_unknown: false)#RDL::Globals.info.get(klass, meth, :type)
          if types
            
            return false unless types.any? { |tlm|
              blk_typ = tlm.block.is_a?(RDL::Type::MethodType) ? tlm.block.args + [tlm.block.ret] : [tlm.block]
              if (tlm.args + blk_typ + [tlm.ret]).any? { |t| t.is_a? ComputedType }
              ## In this case, need to actually evaluate the ComputedType.
              ## Going to do this using the receiver `left` and the args from `t`
                ## If subtyping holds for this, then we know `left` does indeed have a method of the relevant type.
                computed_tlm = RDL::Typecheck.compute_types(tlm, klass, left, t.args)
                leq(computed_tlm.instantiate(base_inst.merge({ self: left })), t, nil, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
              else
                leq(tlm.instantiate(base_inst.merge({ self: left})), t, nil, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
              end
            }
          end
        }
        return true
      end
      # Note we do not allow raw subtyping leq(GenericType, NominalType, ...)

      # method
      if left.is_a?(MethodType) && right.is_a?(MethodType)
        inst = {} if not inst
        if left.args.last.is_a?(VarargType)
          return false unless right.args.size >= left.args.size
          new_args = right.args[(left.args.size - 1) ..-1]          
          if left.args.size == 1
            left = RDL::Type::MethodType.new(new_args, left.block, left.ret)
          else
            left = RDL::Type::MethodType.new(left.args[0..(left.args.size-2)]+new_args, left.block, left.ret)
          end
        end
        if left.args.last.is_a?(OptionalType) 
            left = RDL::Type::MethodType.new(left.args.map { |t| if t.is_a?(RDL::Type::OptionalType) then t.type else t end }, left.block, left.ret)
          if left.args.size == right.args.size + 1
          ## A method with an optional type in the last position can be used in place
          ## of a method without the optional type. So drop it and then check subtyping.
            left = RDL::Type::MethodType.new(left.args.slice(0, left.args.size-1), left.block, left.ret)
          end
        end
        return false unless left.args.size == right.args.size
        return false unless left.args.zip(right.args).all? { |tl, tr| leq(tr.instantiate(inst), tl.instantiate(inst), inst, !ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) } # contravariance

        if left.block && right.block
          return false unless leq(right.block.instantiate(inst), left.block.instantiate(inst), inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) # contravariance
        elsif (left.block && !left.block.is_a?(VarType) && !right.block) || (right.block && !right.block.is_a?(VarType) && !left.block)
          return false # one has a block and the other doesn't
        end
        return leq(left.ret.instantiate(inst), right.ret.instantiate(inst), inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) # covariance

      end
      return true if left.is_a?(MethodType) && right.is_a?(NominalType) && right.name == 'Proc'

      # structural
      if left.is_a?(StructuralType) && right.is_a?(StructuralType)
        # allow width subtyping - methods of right have to be in left, but not vice-versa
        return right.methods.all? { |m, t|
          # in recursive call set inst to nil since those method types have implicit quantifier
          left.methods.has_key?(m) && leq(left.methods[m], t, nil, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
        }
      end
      # Note we do not allow a structural type to be a subtype of a nominal type or generic type,
      # even though in theory that would be possible.

      # tuple
      if left.is_a?(TupleType) && right.is_a?(TupleType)
        # Tuples are immutable, so covariant subtyping allowed
        return false unless left.params.length == right.params.length
        return false unless left.params.zip(right.params).all? { |lt, rt| leq(lt, rt, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) }
        # subyping check passed
        left.ubounds << right unless no_constraint
        right.lbounds << left unless no_constraint
        return true
      end
      if left.is_a?(TupleType) && right.is_a?(GenericType) && right.base == RDL::Globals.types[:array]
        # TODO !ileft and right carries a free variable
        return false unless left.promote!
        return leq(left, right, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) # recheck for promoted type
      end

      # finite hash
      if left.is_a?(FiniteHashType) && right.is_a?(FiniteHashType)
        # Like Tuples, FiniteHashes are immutable, so covariant subtyping allowed
        # But note, no width subtyping allowed, to match #member?
        right_elts = right.elts.clone # shallow copy
        left.elts.each_pair { |k, tl|
          if right_elts.has_key? k
            tr = right_elts[k]
            if k == :action && tl.is_a?(RDL::Type::VarType)
              if !$blah
                $blah = true
              else
                #raise
              end
            end
            return false if tl.is_a?(OptionalType) && !tr.is_a?(OptionalType) # optional left, required right not allowed, since left may not have key
            tl = tl.type if tl.is_a? OptionalType
            tr = tr.type if tr.is_a? OptionalType
            return false unless leq(tl, tr, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
            right_elts.delete k
          else
            return false unless right.rest && leq(tl, right.rest, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
          end
        }
        right_elts.each_pair { |k, t|
          return false unless t.is_a? OptionalType
        }
        unless left.rest.nil?
          # If left has optional stuff, right needs to accept it
          return false unless !(right.rest.nil?) && leq(left.rest, right.rest, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons)
        end
        left.ubounds << right unless no_constraint
        right.lbounds << left unless no_constraint
        return true
      end
      if left.is_a?(FiniteHashType) && right.is_a?(GenericType) && right.base == RDL::Globals.types[:hash]
        # TODO !ileft and right carries a free variable
        return false unless left.promote!
        return leq(left, right, inst, ileft, deferred_constraints, no_constraint: no_constraint, ast: ast, propagate: propagate, new_cons: new_cons) # recheck for promoted type
      end

      ## precise string
      if left.is_a?(PreciseStringType)
        if right.is_a?(PreciseStringType)
          return false if left.vals.size != right.vals.size
          left.vals.each_with_index { |v, i|
            if v.is_a?(String) && right.vals[i].is_a?(String)
              return false unless v == right.vals[i]
            elsif v.is_a?(Type) && right.vals[i].is_a?(Type)
              return false unless v <= right.vals[i]
            else
              return false
            end
          }
          left.ubounds << right unless no_constraint
          right.lbounds << left unless no_constraint
          return true
        elsif right == RDL::Globals.types[:string]
          return false unless left.promote!
          return true
        elsif right.is_a?(NominalType) && String.ancestors.include?(RDL::Util.to_class(right.name))
          ## necessary because of checking agains union types: we don't want to promote! unless it will work
          left.promote!
          return true
        end
      end

      return false
    end
  end

  # [+ a +] is an Array<Type> that may contain union types.
  # returns Array<Array<Type>> containing all possible expansions of the union types.
  # For example, slightly abusing notation:
  #
  # expand_product [A, B]           #=> [[A, B]]
  # expand_product [A or B, C]      #=> [[A, C], [B, C]]
  # expand_product [A or B, C or D] #=> [[A, C], [B, C], [A, D], [B, D]]
  def self.expand_product(a)
    return [[]] if a.empty? # logic below only applies if at least one element
    a.map! { |t| t.canonical }
    counts = a.map { |t| if t.is_a? UnionType then t.types.length - 1 else 0 end }
    res = []
    # now iterate through ever combination of indices
    # using combinations is not quite as memory efficient as inlining that code here,
    # but it's a lot easier to think about combinations separate from this code
    combinations(counts).each { |inds|
      tmp = []
      # set tmp to be a with elts in positions in ind selected from unions
      a.each_with_index { |t, i| if t.is_a? UnionType then tmp << t.types[inds[i]] else tmp << t end }
      res << tmp
    }
    return res
#    return [a]
  end

private

  # [+ a +] is Array<Integer>
  # returns Array<Array<Integer>> containing all combinations of 0..a[i] at index i
  # For example:
  #
  # combinations [0, 0]  #=> [[0, 0]]
  # combinations [1, 0]  #=> [[0, 0], [1, 0]]
  # combinations [1, 1]  #=> [[0, 0], [0, 1][, [1, 0], [1, 1]]]
  #
  # yes, this is used in expand_product above!
  def self.combinations(a)
    cur = a.map { |x| 0 }
    res = []
    while ((cur <=> a) < 1) # Array#<=> uses lexicographic order, so this will repeat until cur == a
      res << cur.dup
      i = cur.length - 1 # start at right since want next in lexicographic order
      while i >= 0
        cur[i] += 1
        break if (cur[i] <= a[i]) # increment did not overflow position, or it overflowed in position 0 so allow inc to break outer loop
        cur[i] = 0 unless i == 0 # increment overflowed; reset to 0 and continue looping, except allow overflow to exit when i == 0
        i -= 1
      end
    end
    return res
  end

end
