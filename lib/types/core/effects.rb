class Read; end
class Write; end
RDL.type_params :Write, [:t], :all?
RDL.type_params :Read, [:t], :all?
RDL.type_params :Idem, [:t], :all?
class Issue; end
class Customer; end
class Payment; end
class Event; end
class Idem < Write; end