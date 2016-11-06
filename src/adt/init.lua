local Fun  = require "fun"

local Sort      = setmetatable ({}, { __tostring = function () return "Sort"      end })
local Variable  = setmetatable ({}, { __tostring = function () return "Variable"  end })
local Operation = setmetatable ({}, { __tostring = function () return "Operation" end })
local Axiom     = setmetatable ({}, { __tostring = function () return "Axiom"     end })
local Term      = setmetatable ({}, { __tostring = function () return "Term"      end })

local Generator = {}
local Name      = {}
local Axioms    = {}

-- ## Sort

Sort.__index = Sort

getmetatable (Sort).__call = function (_, name)
  return setmetatable ({
    [Name  ] = name,
    [Axioms] = {},
  }, Sort)
end

function Sort.__tostring (sort)
  return tostring (sort [Name])
end

function Sort.generators (t)
  assert (type (t) == "table",
          "parameter must be a table of generators")
  Fun.fromtable (t)
    : each (function (x)
              assert (getmetatable (x) == Operation,
                      "parameters must be operations")
            end)
  Fun.fromtable (t)
    : each (function (x) x [Generator] = true end)
end

-- ## Variable

Variable.__index = Variable

getmetatable (Variable).__call = function (_, t)
  assert (type (t) == "table")
  local result = setmetatable ({
    [Name] = t [Name],
    [Sort] = t [Sort],
  }, Variable)
  return result
end

function Variable.__tostring (variable)
  return tostring (variable [Name]) .. ": " .. tostring (variable [Sort])
end

-- ## Operation

function Sort.__index (sort, key)
  if rawget (Sort, key)
  or (type (key) == "string" and key:match "^__") then
    return rawget (Sort, key)
  elseif key:match "^_" then
    local result = Variable {
      [Name] = key:match "^_(.*)$",
      [Sort] = sort,
    }
    rawset (sort, key, result)
    return result
  end
end

function Sort.__newindex (sort, key, t)
  if type (t) == "table" then
    Fun.frommap (t):each (function (k, s)
      assert (getmetatable (s) == Sort, tostring (k) .. " must be a sort")
    end)
    local result = setmetatable ({
      [Name] = key,
      [Sort] = sort,
    }, Operation)
    Fun.frommap (t):each (function (k, v)
      result [k] = v
    end)
    rawset (sort, key, result)
  else
    rawset (sort, key, t)
  end
end

function Operation.__eq (lhs, rhs)
  return Fun.frommap (lhs)
         : all (function (k, v) return rhs [k] == v end)
     and Fun.frommap (rhs)
         : all (function (k, v) return lhs [k] == v end)
end

function Operation.__tostring (operation)
  local t = Fun.frommap (operation)
          : filter  (function (k, _   ) return type (k) ~= "table" end)
          : map     (function (k, sort) return tostring (k) .. ": " .. tostring (sort) end)
          : totable ()
  return tostring (operation [Name])
      .. (#t == 0 and "" or " { " .. table.concat (t, ", ") .. " }")
      .. ": "
      .. tostring (operation [Sort])
end

function Operation.__call (operation, t)
  local result = setmetatable ({
    [Operation] = operation,
    [Name     ] = operation [Name],
    [Sort     ] = operation [Sort],
  }, Term)
  Fun.frommap (t):each (function (k, v)
    assert (operation [k],
            tostring (k) .. " must be a field of " .. tostring (operation [Name]))
    assert (getmetatable (v) == Term or getmetatable (v) == Variable,
            tostring (k) .. " must be a term or a variable")
    if getmetatable (v) == Term then
      assert (v [Sort] == operation [k],
              tostring (k) .. " must be of sort " .. tostring (operation [k]))
    elseif getmetatable (v) == Variable then
      assert (v [Sort] == operation [k],
              tostring (k) .. " must be of sort " .. tostring (operation [k]))
    end
    result [k] = v
  end)
  return result
end

-- ## Term

Term.__index = Term

function Term.__tostring (term)
  local t = Fun.frommap (term)
          : filter  (function (k, _) return type (k) ~= "table" end)
          : map     (function (k, t) return tostring (k) .. " = " .. tostring (t) end)
          : totable ()
  return tostring (term [Name])
      .. (#t == 0 and "" or " { " .. table.concat (t, ", ") .. " }")
      .. ": " .. tostring (term [Sort])
end

function Term.__eq (lhs, rhs)
  if getmetatable (lhs) ~= getmetatable (rhs) then
    return false
  end
  assert (getmetatable (lhs) == Term,
          "lhs must be a term or a variable")
  assert (getmetatable (rhs) == Term,
          "rhs must be a term or a variable")
  return Fun.frommap (lhs)
         : all (function (k, v) return rhs [k] == v end)
     and Fun.frommap (rhs)
         : all (function (k, v) return lhs [k] == v end)
end

function Term.equivalence (lhs, rhs)
  assert (getmetatable (lhs) == Term or getmetatable (lhs) == Variable,
          "lhs must be a term or a variable")
  assert (getmetatable (rhs) == Term or getmetatable (rhs) == Variable,
          "rhs must be a term or a variable")
  if lhs [Sort] ~= rhs [Sort] then
    return nil
  end
  local variables = {}
  local function compare (l, r)
    local result
    if  getmetatable (l) == Variable
    and getmetatable (r) == Variable then
      if (variables [l] and variables [l] ~= r)
      or (variables [r] and variables [r] ~= l) then
        result = false
      else
        variables [l] = r
        variables [r] = l
        result = true
      end
    elseif getmetatable (l) == Variable
       and getmetatable (r) == Term then
      if variables [l] and variables [l] ~= r then
        result = false
      else
        variables [l] = r
        result = true
      end
    elseif getmetatable (l) == Term
       and getmetatable (r) == Variable then
      if variables [r] and variables [r] ~= l then
        result = false
      else
        variables [r] = l
        result = true
      end
    elseif getmetatable (l) == Term
       and getmetatable (r) == Term then
      if l [Operation] == r [Operation] then
        result = Fun.frommap (l [Operation])
          : filter (function (k) return type (k) ~= "table" end)
          : all (function (k) return compare (l [k], r [k]) end)
      else
        result = false
      end
    end
    return result
  end
  return compare (lhs, rhs), variables
end

function Term.__div (term, mapping)
  assert (getmetatable (term) == Term or getmetatable (term) == Variable,
          "term must be a term or a variable")
  assert (type (mapping) == "table")
  Fun.frommap (mapping):each (function (k, v)
    assert (getmetatable (k) == Variable,
            tostring (k) .. " must be a variable")
    assert (getmetatable (v) == Variable or getmetatable (v) == Term,
            tostring (k) .. " must be a term or a variable")
  end)
  local function rename (t)
    local result
    if getmetatable (t) == Variable then
      result = mapping [t] or t
    else
      result = t [Operation] (Fun.frommap (t)
        : filter  (function (k, _) return type (k) ~= "table" end)
        : map     (function (k, v) return k, rename (v) end)
        : tomap ())
    end
    return result
  end
  return rename (term)
end

Variable.__div = Term.__div

-- ## Axiom

getmetatable (Axiom).__call = function (_, t)
  assert (type (t) == "table",
          "Axiom takes a table as parameter")
  assert (t.when == nil or getmetatable (t.when) == Term,
          "when must be a Boolean term")
  assert (#t == 2,
          "axiom must be between two terms")
  local result = setmetatable ({}, Axiom)
  Fun.frommap (t):each (function (k, v)
    if type (k) == "number" then
      assert (getmetatable (v) == Term or getmetatable (v) == Variable,
              tostring (k) .. " must be a term or a variable")
    end
    result [k] = v
  end)
  return result
end

function Axiom.__tostring (axiom)
  local t = Fun.fromtable (axiom)
          : map (function (x) return tostring (x) end)
          : totable ()
  return table.concat (t, " = ")
      .. (axiom.when and " when " .. tostring (axiom.when) or "")
end

function Axiom.__eq (lhs, rhs)
  return Fun.frommap (lhs)
         : all (function (k, v) return rhs [k] == v end)
     and Fun.frommap (rhs)
         : all (function (k, v) return lhs [k] == v end)
end

-- # Adt

return {
  name      = Name,
  generator = Generator,
  axioms    = Axioms,
  Sort      = Sort,
  Variable  = Variable,
  Operation = Operation,
  Term      = Term,
  Axiom     = Axiom,
  axiom     = function (...) return getmetatable (Axiom).__call (Axiom, ...) end,
}
