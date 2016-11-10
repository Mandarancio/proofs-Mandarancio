local Fun     = require "fun"
local Hashids = require "hashids"
local Adt     = require "adt"
local Boolean = require "adt.boolean"

local hash = Hashids.new ("modeling & verification", 4)

local Theorem    = setmetatable ({}, { __tostring = function () return "Theorem"    end })
local Conjecture = setmetatable ({}, { __tostring = function () return "Conjecture" end })

Theorem.Conjecture = Conjecture

local Variables = setmetatable ({}, { __mode = "v" })

local function simplify (term)
  assert (getmetatable (term) == Adt.Term,
          "parameter must be a term")
  assert (term [Adt.Sort] == Boolean,
          "parameter must be a Boolean")
  if term == Boolean.True {} then
    return nil
  else
    return term
  end
end

local function rename (term, variables)
  if getmetatable (term) == Adt.Variable then
    if not variables [term] then
      variables [term] = Adt.Variable {
        [Adt.Sort] = term [Adt.Sort],
        [Adt.name] = hash:encode (#Variables+1)
      }
      Variables [#Variables+1] = variables [term]
    end
    return variables [term]
  else
    return term [Adt.Operation] (Fun.frommap (term)
      : filter  (function (k, _) return type (k) ~= "table" end)
      : map     (function (k, t) return k, rename (t, variables) end)
      : tomap   ())
  end
end

local function all_variables (x, variables)
  variables = variables or {}
  if getmetatable (x) == Adt.Axiom
  or getmetatable (x) == Theorem
  or getmetatable (x) == Conjecture then
    all_variables (x.when, variables)
    all_variables (x [1] , variables)
    all_variables (x [2] , variables)
  elseif getmetatable (x) == Adt.Variable then
    variables [x] = x
  elseif getmetatable (x) == Adt.Term then
    Fun.frommap (x)
      : filter (function (k, _) return type (k) ~= "table" end)
      : each   (function (_, t) all_variables (t, variables) end)
  end
  return variables
end

getmetatable (Theorem).__call = function (_, t)
  assert (type (t) == "table",
          "Theorem takes a table as parameter")
  assert ( t.when == nil
        or (getmetatable (t.when) == Adt.Term and t.when [Adt.Sort] == Boolean),
          "when must be a Boolean term")
  assert (#t == 2,
          "theorem must be between two terms")
  assert (getmetatable (t [1]) == Adt.Term or getmetatable (t [1]) == Adt.Variable,
          "lhs must be a term or a variable")
  assert (getmetatable (t [2]) == Adt.Term or getmetatable (t [2]) == Adt.Variable,
          "rhs must be a term or a variable")
  local variables = {}
  local when      = t.when and simplify (t.when)
  local result    = setmetatable ({
    variables = {},
    when = when and rename (when, variables),
    [1]  = rename (t [1], variables),
    [2]  = rename (t [2], variables),
  }, Theorem)
  for k, v in pairs (t.variables or {}) do
    result.variables [k] = variables [v]
  end
  return result
end

getmetatable (Conjecture).__call = function (_, t)
  assert (type (t) == "table",
          "Conjecture takes a table as parameter")
  assert ( t.when == nil
        or (getmetatable (t.when) == Adt.Term and t.when [Adt.Sort] == Boolean),
          "when must be a Boolean term")
  assert (#t == 2,
          "conjecture must be between two terms")
  assert (getmetatable (t [1]) == Adt.Term or getmetatable (t [1]) == Adt.Variable,
          "lhs must be a term or a variable")
  assert (getmetatable (t [2]) == Adt.Term or getmetatable (t [2]) == Adt.Variable,
          "rhs must be a term or a variable")
  local when      = t.when and simplify (t.when)
  local variables = {}
  if when then
    all_variables (when, variables)
  end
  all_variables (t [1], variables)
  all_variables (t [2], variables)
  local result    = setmetatable ({
    variables = variables,
    when = when and rename (when, variables),
    [1]  = rename (t [1], variables),
    [2]  = rename (t [2], variables),
  }, Conjecture)
  return result
end

function Theorem.__tostring (axiom)
  local t = Fun.fromtable (axiom)
          : map (function (x) return tostring (x) end)
          : totable ()
  return table.concat (t, " = ")
      .. (axiom.when and " when " .. tostring (axiom.when) or "")
end

function Theorem.__eq (lhs, rhs)
  return Adt.Term.equivalence (lhs [1] , rhs [1] )
     and Adt.Term.equivalence (lhs [2] , rhs [2] )
     and (lhs.when and rhs.when and Adt.Term.equivalence (lhs.when, rhs.when)
          or lhs.when == rhs.when)
end

function Theorem.conjecture (conjecture)
  assert (getmetatable (conjecture) == Conjecture,
          "parameter must be an conjecture")
  return Theorem {
    variables = all_variables (conjecture),
    when = conjecture.when,
    [1]  = conjecture [1],
    [2]  = conjecture [2],
  }
end

function Theorem.axiom (axiom)
  assert (getmetatable (axiom) == Adt.Axiom,
          "parameter must be an axiom")
  return Theorem {
    variables = all_variables (axiom),
    when = axiom.when,
    [1]  = axiom [1],
    [2]  = axiom [2],
  }
end

function Theorem.reflexivity (term)
  assert (getmetatable (term) == Adt.Term or getmetatable (term) == Adt.Variable,
          "parameter must be a term or a variable")
  return Theorem {
    variables = all_variables (term),
    [1] = term,
    [2] = term,
  }
end

function Theorem.symmetry (theorem)
  assert (getmetatable (theorem) == Theorem,
          "parameter must be a theorem")
  return Theorem {
    variables = all_variables (theorem),
    when = theorem.when,
    [1]  = theorem [2],
    [2]  = theorem [1],
  }
end

function Theorem.transitivity (lhs, rhs)
  assert (getmetatable (lhs) == Theorem,
          "lhs must be a theorem")
  assert (getmetatable (rhs) == Theorem,
          "rhs must be a theorem")
  local ok, variables = Adt.Term.equivalence (lhs [2], rhs [1])
  if ok then
    local when
    if lhs.when and rhs.when then
      when = Boolean.And {
        lhs.when,
        rhs.when / variables,
      }
    elseif lhs.when then
      when = lhs.when
    elseif rhs.when then
      when = rhs.when / variables
    end
    local result = Theorem {
      variables = all_variables (lhs),
      when = when,
      [1]  = lhs [1],
      [2]  = rhs [2] / variables,
    }
    return result
  else
    return nil, "lhs [2] ~= rhs [1]"
  end
end

function Theorem.substitutivity (operation, operands)

  assert (getmetatable (operation) == Adt.Operation,
          "operation must be a term")
  assert (type (operands) == "table",
          "operands must be a table")

  Fun.frommap (operands)
    : each (function (k, v)
              assert (getmetatable (v) == Theorem,
                      tostring (k) .. " must be a theorem")
            end)
  local variables = {}
  Fun.frommap (operands)
    : each (function (_, v) all_variables (v, variables) end)
  -- TODO: apply `operation` on left and right part of `operands`
  local lhs;
  local rhs;
  if (#operands==1) then
    lhs = operation{operands[1][1]};
    rhs = operation{operands[1][2]};
  elseif (#operands==2) then
    lhs = operation{operands[1][1],operands[2][1]};
    rhs = operation{operands[1][2],operands[2][2]};
  end


  return Theorem {
    variables = variables,
    [1]  = lhs,
    [2]  = rhs,
  }
end

function Theorem.substitution (theorem, variable, replacement)
  assert (getmetatable (theorem) == Theorem,
          "theorem must be a term")
  assert (getmetatable (variable) == Adt.Variable,
          "variable must be a variable")
  assert (getmetatable (replacement) == Adt.Term or getmetatable (replacement) == Adt.Variable,
          "replacement must be a term or a variable")
  assert (variable [Adt.Sort] == replacement [Adt.Sort],
          "variable and replacement must be of the same sort")
  -- TODO: repolace `variable` by `replacement` in `theorem`



  local lhs = theorem[1];
  local rhs = theorem[2];

  local mapping = {};
  mapping[variable]=replacement;
  lhs = lhs / mapping;
  rhs = rhs / mapping;

  return Theorem {
    variables = all_variables (theorem),
    when = theorem.when,
    [1]  = lhs,
    [2]  = rhs,
  }
end

function Theorem.cut (theorem, replacement)
  assert (getmetatable (theorem) == Theorem,
          "theorem must be a term")
  assert (getmetatable (replacement) == Theorem,
          "replacement must be a theorem")
  if not theorem.when then
    return nil
  end
  local search = Boolean.Equals {
    replacement [1],
    replacement [2],
  }
  local replaced = false
  local function replace (term)
    if getmetatable (term) == Adt.Variable then
      return term
    end
    local ok, map = Adt.Term.equivalence (term, search)
    if ok then
      replaced = true
      return replacement.when
         and replacement.when / map
          or Boolean.True {}
    else
      return term [Adt.Operation] (Fun.frommap (term)
        : filter  (function (k, _) return type (k) ~= "table" end)
        : map     (function (k, t) return k, replace (t) end)
        : tomap ())
    end
  end
  local result = replace (theorem.when)
  if not replaced then
    return nil
  end
  return Theorem {
    variables = all_variables (theorem),
    when = result,
    theorem [1],
    theorem [2],
  }
end

function Theorem.inductive (conjecture, variable, t)
  assert (getmetatable (conjecture) == Conjecture,
          "conjecture must be a conjecture")
  assert (getmetatable (variable) == Adt.Variable,
          "variable must be a variable")
  assert (type (t) == "table")
  local generators = Fun.frommap (variable [Adt.Sort])
    : filter (function (_, v) return getmetatable (v) == Adt.Operation and v [Adt.generator] end)
  local result  = Theorem.conjecture (conjecture)
  local missing = {}
  generators:filter (function (key)
    return type (t [key]) ~= "function"
  end):map (function (k) return tostring (k) end):totable ()
  if #missing ~= 0 then
    return nil, table.concat (missing, ", ")
  end
  if generators:all (function (_, operation)
    -- TODO: check that the theorem built by applying `operation` on `variable`
    -- corresponds to the conjecture.
    local mapping = {}
    if #operation==0 then
      mapping[variable]=operation{};
    else
      mapping[variable]=operation{variable};
    end
    local lhs = conjecture[1];
    local rhs = conjecture[2];
    lhs = lhs / mapping;
    rhs = rhs / mapping;
    local teo = Theorem{lhs,rhs}
    local r = t[operation](teo)
    -- print('\n----\n')
    -- print(r)
    -- print(teo)
    -- print(r==teo)
    -- print('\n----\n')
    return r==teo;
  end) then
    return result
  else
    return nil
  end
end

return Theorem
