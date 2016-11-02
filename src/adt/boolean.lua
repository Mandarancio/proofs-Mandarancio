local Adt     = require "adt"
local Boolean = Adt.Sort "bool"

Boolean.True    = {}
Boolean.False   = {}
Boolean.Equals  = { Boolean, Boolean }
Boolean.Not     = { Boolean }
Boolean.And     = { Boolean, Boolean }
Boolean.Or      = { Boolean, Boolean }
Boolean.Xor     = { Boolean, Boolean }
Boolean.Implies = { Boolean, Boolean }

Boolean.generators { Boolean.True, Boolean.False }

-- Not
Boolean [Adt.axioms].not_true = Adt.axiom {
  Boolean.Not { Boolean.True {} },
  Boolean.False {}
}
Boolean [Adt.axioms].not_false = Adt.axiom {
  Boolean.Not { Boolean.False {} },
  Boolean.True {},
}

-- TODO: define axioms for other operations
Boolean [Adt.axioms].equals_true = Adt.axiom {
  Boolean.Equals {Boolean.True{} , Boolean.True{}},
  Boolean.True{},
}

Boolean [Adt.axioms].equals_false = Adt.axiom {
  Boolean.Equals {Boolean.False{} , Boolean.False{}},
  Boolean.True{},
}
Boolean [Adt.axioms].equals_xy = Adt.axiom{
  Boolean.Equals {Boolean.True{} , Boolean.False{}},
  Boolean.False{},
}

Boolean [Adt.axioms].equals_yx = Adt.axiom{
  Boolean.Equals {Boolean.False{} , Boolean.True{}},
  Boolean.False{},
}

Boolean [Adt.axioms].and_true_true = Adt.axiom{
  Boolean.And {Boolean.True{}, Boolean.False{}},
  Boolean.True{},
}

Boolean [Adt.axioms].and_false_x = Adt.axiom{
  Boolean.And {Boolean.False{}, Boolean._x},
  Boolean.False{},
}

Boolean [Adt.axioms].and_x_false = Adt.axiom{
  Boolean.And {Boolean._x, Boolean.False{}},
  Boolean.False{},
}

Boolean [Adt.axioms].or_false_false = Adt.axiom{
  Boolean.Or {Boolean.False{},Boolean.False{}},
  Boolean.False{},
}

Boolean [Adt.axioms].or_true_x = Adt.axiom{
  Boolean.Or {Boolean.True{}, Boolean._x},
  Boolean.True{},
}

Boolean [Adt.axioms].or_x_true = Adt.axiom{
  Boolean.Or {Boolean._x, Boolean.True{}},
  Boolean.True{},
}

Boolean [Adt.axioms].xor_false = Adt.axiom{
  Boolean.Xor {Boolean._x,Boolean._y},
  Boolean.False{},
  when=Boolean.Equals{Boolean._x, Boolean._y}
}

Boolean [Adt.axioms].xor_true = Adt.axiom{
  Boolean.Xor {Boolean._x, Boolean._y},
  Boolean.True {},
  when=Boolean.Not{Boolean.Equals{Boolean._x,Boolean._y}} -- It will work??
}

Boolean [Adt.axioms].implies_true_false = Adt.axiom{
  Boolean.Implies{ Boolean.True{}, Boolean.False{}},
  Boolean.False{},
}

Boolean [Adt.axioms].implies_true = Adt.axiom{
  Boolean.Implies{ Boolean._x, Boolean._y},
  Boolean.True{},
  when= Boolean.Or{Boolean.Equals{Boolean._x,Boolean._y}, Boolean.Equals{Boolean._y,Boolean.True{}}} --?
}

return Boolean
