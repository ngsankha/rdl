RDL.nowrap :Module

RDL.type :Module, 'self.constants', '() -> Array<Integer>' # also constants(inherited), but undocumented
RDL.type :Module, 'self.nesting', '() -> Array<Module>'
RDL.type :Module, :initialize, '() -> self'
RDL.type :Module, :initialize, '() { (Module) -> %any } -> self'

RDL.type :Module, :<, '(Module other) -> %bool or nil'
RDL.type :Module, :<=, '(Module other) -> %bool or nil'
RDL.type :Module, :<=>, '(Module other) -> -1 or 0 or 1 or nil'
RDL.type :Module, :==, '(%any other) -> %bool'
RDL.type :Module, :equal?, '(%any other) -> %bool'
RDL.type :Module, :eql?, '(%any other) -> %bool'
RDL.type :Module, :===, '(%any other) -> %bool'
RDL.type :Module, :>, '(Module other) -> %bool or nil'
RDL.type :Module, :>=, '(Module other) -> %bool or nil'
RDL.type :Module, :ancestors, '() -> Array<Module>'
RDL.type :Module, :autoload, '(Symbol module, String filename) -> nil'
RDL.type :Module, :autoload?, '(Symbol name) -> String or nil'
RDL.type :Module, :class_eval, '(String, ?String filename, ?Integer lineno) -> %any'
RDL.type :Module, :class_exec, '(*%any args) { (*%any args) -> %any } -> %any'
RDL.type :Module, :class_variable_defined?, '(Symbol or String) -> %bool'
RDL.type :Module, :class_variable_get, '(Symbol or String) -> %any'
RDL.type :Module, :class_variable_set, '(Symbol or String, %any) -> %any'
RDL.type :Module, :class_variables, '(?%bool inherit) -> Array<Symbol>'
RDL.type :Module, :const_defined?, '(Symbol or String, ?%bool inherit) -> %bool'
RDL.type :Module, :const_get, '(Symbol or String, ?%bool inherit) -> %any'
RDL.type :Module, :const_missing, '(Symbol) -> %any'
RDL.type :Module, :const_set, '(Symbol or String, %any) -> %any'
RDL.type :Module, :constants, '(?%bool inherit) -> Array<Symbol>'
RDL.type :Module, :freeze, '() -> self'
RDL.type :Module, :include, '(*Module) -> self'
RDL.type :Module, :include?, '(Module) -> %bool'
RDL.type :Module, :included_modules, '() -> Array<Module>'
RDL.rdl_alias :Module, :inspect, :to_s
RDL.type :Module, :instance_method, '(Symbol) -> UnboundMethod'
RDL.type :Module, :instance_methods, '(?%bool include_super) -> Array<Symbol>'
RDL.type :Module, :method_defined?, '(Symbol or String) -> %bool'
RDL.type :Module, :module_eval, '(String, ?String filename, ?Integer lineno) -> %any' # matches rdoc example but not RDL.type
RDL.type :Module, :module_exec, '(*%any args) { (*%any args) -> %any } -> %any'
RDL.type :Module, :name, '() -> String'
RDL.type :Module, :prepend, '(*Module) -> self'
RDL.type :Module, :private_class_method, '(*(Symbol or String)) -> self'
RDL.type :Module, :private_constant, '(*Symbol) -> self'
RDL.type :Module, :private_instance_methods, '(?%bool include_super) -> Array<Symbol>'
RDL.type :Module, :private_method_defined?, '(Symbol or String) -> %bool'
RDL.type :Module, :protected_instance_methods, '(?%bool include_super) -> Array<Symbol>'
RDL.type :Module, :protected_method_defined?, '(Symbol or String) -> %bool'
RDL.type :Module, :public_class_method, '(*(Symbol or String)) -> self'
RDL.type :Module, :public_constant, '(*Symbol) -> self'
RDL.type :Module, :public_instance_method, '(Symbol) -> UnboundMethod'
RDL.type :Module, :public_instance_methods, '(?%bool include_super) -> Array<Symbol>'
RDL.type :Module, :public_method_defined?, '(Symbol or String) -> %bool'
RDL.type :Module, :remove_class_variable, '(Symbol) -> %any'
RDL.type :Module, :singleton_class?, '() -> %bool'
RDL.type :Module, :to_s, '() -> String'
# private methods below here
RDL.type :Module, :alias_method, '(Symbol new_name, Symbol old_name) -> self'
RDL.type :Module, :append_features, '(Module) -> self'
RDL.rdl_alias :Module, :attr, :attr_reader
RDL.type :Module, :attr_accessor, '(*(Symbol or String)) -> nil'
RDL.type :Module, :attr_reader, '(*(Symbol or String)) -> nil'
RDL.type :Module, :attr_writer, '(*(Symbol or String)) -> nil'
RDL.type :Module, :define_method, '(Symbol, Method) -> Symbol'
RDL.type :Module, :define_method, '(Symbol) { (*%any) -> %any } -> Symbol'
RDL.type :Module, :extend_object, '(%any) -> %any'
RDL.type :Module, :extended, '(Module othermod) -> %any'
RDL.type :Module, :included, '(Module othermod) -> %any'
RDL.type :Module, :method_added, '(Symbol method_name) -> %any'
RDL.type :Module, :method_removed, '(Symbol method_name) -> %any'
RDL.type :Module, :module_function, '(*(Symbol or String)) -> self'
RDL.type :Module, :prepend_features, '(Module) -> self'
RDL.type :Module, :prepended, '(Module othermod) -> %any'
RDL.type :Module, :private, '(*(Symbol or String)) -> self'
RDL.type :Module, :protected, '(*(Symbol or String)) -> self'
RDL.type :Module, :public, '(*(Symbol or String)) -> self'
RDL.type :Module, :refine, '(Class) { (%any) -> %any } -> self' # ??
RDL.type :Module, :remove_const, '(Symbol) -> %any'
RDL.type :Module, :remove_method, '(Symbol or String) -> self'
RDL.type :Module, :undef_method, '(Symbol or String) -> self'
RDL.type :Module, :using, '(Module) -> self'
