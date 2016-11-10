local assert  = require "luassert"
local Adt     = require "adt"
local Boolean = require "adt.boolean"
local Natural = require "adt.natural"
local Theorem = require "adt.theorem"

describe ("#theorem", function ()

  it ("can create a theorem without a condition", function ()
    local theorem = Theorem {
      Boolean.True {},
      Boolean.True {},
    }
    assert.are.equal (getmetatable (theorem), Theorem)
  end)

  it ("can create a theorem with a condition", function ()
    local theorem = Theorem {
      Boolean.True {},
      Boolean.True {},
      when = Boolean.True {},
    }
    assert.are.equal (getmetatable (theorem), Theorem)
  end)

  it ("can print a theorem", function ()
    local theorem = Theorem {
      Boolean.True {},
      Boolean.True {},
      when = Boolean.True {},
    }
    assert.are.equal (tostring (theorem), "True: bool = True: bool")
  end)

  it ("can check if two theorems are equal", function ()
    local t1 = Theorem {
      Boolean.True {},
      Boolean.True {},
    }
    local t2 = Theorem {
      Boolean.True {},
      Boolean.True {},
    }
    local t3 = Theorem {
      Boolean.True {},
      Boolean.True {},
      when = Boolean.False {},
    }
    assert.are    .equal (t1, t2)
    assert.are_not.equal (t1, t3)
  end)

  it ("can apply axiom", function ()
    local theorem = Theorem.axiom (Boolean [Adt.axioms].not_true)
    assert.are.equal (getmetatable (theorem), Theorem)
    assert.are.equal (theorem [1] , Boolean [Adt.axioms].not_true [1] )
    assert.are.equal (theorem [2] , Boolean [Adt.axioms].not_true [2] )
    assert.are.equal (theorem.when, Boolean [Adt.axioms].not_true.when)
  end)

  it ("can apply reflexivity", function ()
    local theorem = Theorem.reflexivity (Boolean.Not { Boolean._x })
    assert.are.equal (getmetatable (theorem), Theorem)
    assert.are.equal (theorem, Theorem {
      Boolean.Not { Boolean._y },
      Boolean.Not { Boolean._y },
    })
  end)

  it ("can apply symmetry", function ()
    local theorem = Theorem.symmetry (Theorem {
      Boolean.True  {},
      Boolean.Not { Boolean.False {} },
    })
    assert.are.equal (getmetatable (theorem), Theorem)
    assert.are.equal (theorem, Theorem {
      Boolean.Not { Boolean.False {} },
      Boolean.True  {},
    })
  end)

  it ("can apply symmetry on equal", function()
    local theorem = Theorem.symmetry (Theorem {
      Boolean.True  {},
      Boolean.Equals { Boolean.False{}, Boolean.False {} },
    })
    assert.are.equal (getmetatable(theorem), Theorem)
    assert.are.equal (theorem, Theorem {
      Boolean.Equals{ Boolean.False{},Boolean.False{}},
      Boolean.True{},
    })
  end)

  it ("can apply transitivity", function ()
    local t1 = Theorem {
      Boolean._v,
      Boolean.Not { Boolean.Not { Boolean._v } },
    }
    local t2 = Theorem {
      Boolean.Not { Boolean.Not { Boolean._w } },
      Boolean._w,
    }
    local theorem = Theorem.transitivity (t1, t2)
    assert.are.equal (getmetatable (theorem), Theorem)
    assert.are.equal (theorem, Theorem {
      Boolean._x,
      Boolean._x,
    })
  end)

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

  it ("can apply cut", function ()
    local t1 = Theorem {
      Boolean.True {},
      Boolean.True {},
      when = Boolean.Equals {
        Boolean._v,
        Boolean.Not { Boolean.Not { Boolean._v } },
      },
    }
    local t2 = Theorem {
      Boolean._x,
      Boolean.Not { Boolean.Not { Boolean._x } },
    }
    local theorem = Theorem.cut (t1, t2)
    assert.are.equal (getmetatable (theorem), Theorem)
    assert.are.equal (theorem, Theorem {
      Boolean.True {},
      Boolean.True {},
    })
  end)

  it ("can check a simple proof", function ()
    -- x + 0 = x
    local t1 = Theorem.axiom (Natural [Adt.axioms].addition_zero)
    -- x + s(y) = s(x + y)
    local t2 = Theorem.axiom (Natural [Adt.axioms].addition_nonzero)
    -- x + s(0) = s(x + 0)
    local t3 = Theorem.substitution (t2, t2.variables [Natural._y], Natural.Zero {})
    -- s(x + 0) = s(x)
    local t4 = Theorem.substitutivity (Natural.Successor, { t1 })
    -- x + s(0) = s(x)
    local t5 = Theorem.transitivity (t3, t4)
    assert.are.equal (getmetatable (t5), Theorem)
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

  it ("can check identity proof", function ()
    -- x + 0 = x
    local t1 = Theorem.axiom (Natural [Adt.axioms].addition_zero)
    -- x + s(y) = s(x + y)
    local t2 = Theorem.axiom (Natural [Adt.axioms].addition_nonzero)
    -- x+0 = 0+x
    local conjecture = Theorem.Conjecture {
      Natural.Addition { Natural._x,Natural.Zero{}},
      Natural.Addition {Natural.Zero{}, Natural._x },
    }
    local theorem = Theorem.inductive (conjecture, conjecture.variables [Natural._x], {
      [Natural.Zero     ] = function (t)
        return t
      end,
      [Natural.Successor] = function (t)
        --s(x)+0 = 0+s(x)
        --s(x)+0 = s(x)
        local t3 = Theorem.substitution(t1, t1.variables[Natural._x], Natural.Successor{Natural._x})
        --0+s(x)=s(0+x)
        local t4 = Theorem.substitution(t2,t2.variables[Natural._x], Natural.Zero{})
        --s(x)+0 = s(0+x)
        local t5 = Theorem.transitivity(t,t4)
        --s(0+x)=s(x)
        local t6 = Theorem.transitivity(Theorem.symmetry(t5),t3)
        --0+s(x)=s(x)
        local t7 = Theorem.transitivity(t4,t6)
        --0+s(x)=s(x)+0
        local t8 = Theorem.transitivity(t7,Theorem.symmetry(t3))
        return Theorem.symmetry(t8)
      end,
    })
    assert.are.equal (getmetatable (theorem), Theorem)
  end)

  it ("can check x+1 = s(x)", function ()
    -- x + 0 = x
    local t1 = Theorem.axiom (Natural [Adt.axioms].addition_zero)
    -- x + s(y) = s(x + y)
    local t2 = Theorem.axiom (Natural [Adt.axioms].addition_nonzero)
    -- 0+x = x+0 =  x(identity of 0, proved before)
    -- local t3 = Theorem.axiom(Adt.axiom{Natural.Addition{Natural.Zero{},Natural._x},Natural._x})
    -- x + s(0) = s(x)
    local conjecture = Theorem.Conjecture {
      Natural.Addition { Natural._x,Natural.Successor{Natural.Zero{}}},
      Natural.Successor{ Natural._x },
    }
    local theorem = Theorem.inductive (conjecture, conjecture.variables [Natural._x], {
      -- 0+s(0)=s(0)
      [Natural.Zero     ] = function ()
        -- x+s(0)=s(x+0)
        local t4 = Theorem.substitution(t2,t2.variables[Natural._y], Natural.Zero{})
        -- 0+s(0) = s(0+0)
        local t5 = Theorem.substitution(t4,t2.variables[Natural._x], Natural.Zero{})
        -- 0+0 = 0
        local t6 = Theorem.substitution(t1,t1.variables[Natural._x], Natural.Zero{})
        -- s(0+0)=s(0)
        local t7 = Theorem.substitutivity(Natural.Successor,{t6})
        -- 0+s(0)=s(0)
        local t8 = Theorem.transitivity(t5,t7)
        return t8
      end,
      -- x+s(0)=s(x)
      [Natural.Successor] = function ()
        -- print("\n####\n")
        -- print(t)
        --x+s(0) =  s(x+0)
        local t4 = Theorem.substitution(t2,t2.variables[Natural._y], Natural.Zero{})
        -- print(t4)
        -- s(x+0)=s(x)
        local t5 = Theorem.substitutivity(Natural.Successor,{t1})
        -- print(t5)
        -- x+s(0)=s(x)
        local t6 = Theorem.transitivity(t4,t5)
        -- print(t6)
        -- print("\n####\n")
        return t6
      end,
    })
    assert.are.equal (getmetatable (theorem), Theorem)
  end)

  it ("can check x + y = y + x", function ()
    -- x + 0 = x
    -- local t1 = Theorem.axiom (Natural [Adt.axioms].addition_zero)
    -- x + s(y) = s(x + y)
    -- local t2 = Theorem.axiom (Natural [Adt.axioms].addition_nonzero)
    -- x + 0 = 0+x as proved before
    local t3 = Theorem.axiom (Adt.axiom{Natural.Addition{Natural._x,Natural.Zero{}}, Natural.Addition{Natural.Zero{},Natural._x}})
    local conjecture = Theorem.Conjecture{
      Natural.Addition{Natural._x, Natural._y},
      Natural.Addition{Natural._y, Natural._x}
    }
    local theorem = Theorem.inductive(conjecture, conjecture.variables[Natural._x],{
      --0+x = x+0
      [Natural.Zero] = function()
        local t4 = Theorem.symmetry(t3)
        return t4
      end,
      [Natural.Successor] = function(t)
        -- no proof
        -- substitutivity donsn't work properly
        -- reflexivity doesn't work properly

        return t
      end
    });
    assert.are.equal (getmetatable (theorem), Theorem)
  end)

end)
