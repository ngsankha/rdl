module RDL::Type
  class AstNode < Type
    attr_reader :op, :val
    attr_accessor :children, :curr, :parent

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
      @children = []
      @curr = self
      @parent = nil
    end

    def root
      unless self.parent
        self
      else
        root(self.parent)
      end
    end

    def insert(child)
      @children << child
      self.root.curr = child
    end

    def find_all(op)
      @children.find_all { |obj| obj.op == op }
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
      [@op, @val.val, [@children.to_s]].inspect
    end

    def <=(other)
      return Type.leq(self, other)
    end

    def member?(obj, *args)
      raise "member? on AstNode called"
    end

    def instantiate(inst)
      return self
    end
  end
end
