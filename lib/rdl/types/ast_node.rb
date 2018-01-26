module RDL::Type
  class AstNode < Type
    attr_reader :val
    # attr_reader :nominal
    attr_accessor :children

    @@cache = {}
    @@cache.compare_by_identity

    class << self
      alias :__new__ :new
    end

    def self.new(op, val)
      t = @@cache[val]
      return t if t
      t = self.__new__ op, val
      return (@@cache[val] = t) # assignment evaluates to t
    end

    def initialize(op, val)
      @op = op
      @val = val
      @children = {}
      # @nominal = NominalType.new(val.class)
    end

    def ==(other)
      return false if other.nil?
      other = other.canonical
      return (other.instance_of? self.class) && (other.val.equal? @val)
    end

    alias eql? ==

    def match(other)
      other = other.canonical
      other = other.type if other.instance_of? AnnotatedArgType
      return true if other.instance_of? WildQuery
      return self == other
    end

    def hash # :nodoc:
      return @val.hash
    end

    def to_s
      "AstNode[#{@val.to_s} [#{@children.to_s}]]"
    end

    def <=(other)
      return Type.leq(self, other)
    end

    def member?(obj, *args)
      t = RDL::Util.rdl_type obj
      return t <= self if t
      obj.equal?(@val)
    end

    def instantiate(inst)
      return self
    end
  end
end
