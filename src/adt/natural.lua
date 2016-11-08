      local Fun     = require "fun"
local Adt     = require "adt"
local Boolean = require "adt.boolean"
local Natural = Adt.Sort "Natural"

Natural.Zero        = {}
Natural.Successor   = { Natural }
Natural.Increment   = { Natural }
Natural.Decrement   = { Natural }
Natural.Addition    = { Natural, Natural }
Natural.Subtraction = { Natural, Natural }
Boolean.Is_even     = { Natural }

Natural.generators { Natural.Zero, Natural.Successor }

function Natural.nth (n)
  return Fun.range (1, n)
       : reduce (function (i) return Natural.Successor { i } end, Natural.Zero {})
end

Natural [Adt.axioms].increment = Adt.axiom {
  Natural.Increment { Natural._v },
  Natural.Successor { Natural._v },
}
Natural [Adt.axioms].addition_zero = Adt.axiom {
  Natural.Addition { Natural._x, Natural.Zero {} },
  Natural._x,
}
Natural [Adt.axioms].addition_nonzero = Adt.axiom {
  Natural.Addition  { Natural._x, Natural.Successor { Natural._y } },
  Natural.Successor { Natural.Addition { Natural._x, Natural._y} },
}

-- TODO: define axioms for other operations

Natural [Adt.axioms].dec_zero = Adt.axiom{
  Natural.Decrement{Natural.Zero{}},
  Natural.Zero{}
}

Natural [Adt.axioms].dec_suc_zero = Adt.axiom{ --it's even need?
  Natural.Decrement{Natural.Successor{Natural.Zero{}}},
  Natural.Zero{}
}

Natural [Adt.axioms].dec_suc_x = Adt.axiom{
  Natural.Decrement{Natural.Successor{Natural._x}},
  Natural._x,
}

Natural [Adt.axioms].sub_0=Adt.axiom{
  Natural.Subtraction{Natural._x,Natural.Zero{}},
  Natural._x
}

Natural [Adt.axioms].sub_nonzero = Adt.axiom{
  Natural.Subtraction{ Natural._x, Natural.Decrement{Natural._y}},
  Natural.Decrement{Natural.Subtraction{Natural._x,Natural._y}}
}

Natural [Adt.axioms].is_even_0 = Adt.axiom{ --is natural at the beginning?
  Boolean.Is_even{Natural.Zero{}},
  Boolean.True{}
}
--
-- Natural [Adt.axioms].is_even_1 = Adt.axioms{
--   Boolean.Is_even{Natural.Successor{Natural.Zero{}}},
--   Boolean.False{}
-- }

Natural [Adt.axioms].is_even_x = Adt.axiom{
  Boolean.Is_even{Natural.Successor{Natural._x}},
  Boolean.Not{Boolean.Is_even{Natural._x}}
}

return Natural
