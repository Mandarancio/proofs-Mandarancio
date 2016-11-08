local assert  = require "luassert"
local Adt     = require "adt"
local Boolean = require "adt.boolean"
local Natural = require "adt.natural"
local Theorem = require "adt.theorem"

describe ("#test", function ()

    it ("can apply substitutivity", function ()
      local t1 = Theorem {
        Boolean.Not { Boolean._w },
        Boolean._w,
      }

      local theorem = Theorem.substitutivity (Boolean.Not, { t1 })
      assert.are.equal (getmetatable (theorem), Theorem)
      assert.are.equal (theorem, Theorem {
        Boolean.Not { Boolean.Not { Boolean._x } },
        Boolean.Not { Boolean._x },
      })
    end)

    it ("can apply substitution", function ()
      local t = Theorem {
        Boolean.Not { Boolean.Not { Boolean._w } },
        Boolean._w,
        when = Boolean.True {},
      }
      local variable = t [2]
      local theorem = Theorem.substitution (t, variable, Boolean.True {})
      assert.are.equal (getmetatable (theorem), Theorem)
      assert.are.equal (theorem, Theorem {
        Boolean.Not { Boolean.Not { Boolean.True {} } },
        Boolean.True {},
        when = Boolean.True {},
      })
    end)

    it ("can check an inductive proof", function ()
      -- x + 0 = x
      local t1 = Theorem.axiom (Natural [Adt.axioms].addition_zero)
      -- x + s(y) = s(x + y)
      local t2 = Theorem.axiom (Natural [Adt.axioms].addition_nonzero)
      -- s(0) + x = s(x)
      local conjecture = Theorem.Conjecture {
        Natural.Addition { Natural.Successor { Natural.Zero {} }, Natural._x },
        Natural.Successor { Natural._x },
      }
      local theorem = Theorem.inductive (conjecture, conjecture.variables [Natural._x], {
        [Natural.Zero     ] = function ()
          -- s(0) + 0 = s(0)
          return Theorem.substitution (t1, t1.variables [Natural._x], Natural.Successor { Natural.Zero {} })
        end,
        [Natural.Successor] = function (t)
          -- s(0) + s(y) = s(s(0) + y)
          local t3 = Theorem.substitution (t2, t2.variables [Natural._x], Natural.Successor { Natural.Zero {} })
          -- s(s(0) + x) = s(s(x))
          local t4 = Theorem.substitutivity (Natural.Successor, { t })
          -- s(0) + s(y) = s(s(y))
          return Theorem.transitivity (t3, t4)
        end,
      })
      assert.are.equal (getmetatable (theorem), Theorem)
    end)


end)
