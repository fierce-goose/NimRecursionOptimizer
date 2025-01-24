import std/macros


type Param = object
      name: NimNode
      paramType: NimNode
      defaultValue: NimNode


const
      routineKinds = {nnkFuncDef, nnkProcDef, nnkMethodDef, nnkIteratorDef}
      callKinds = {nnkCall, nnkCommand}



func deepLast(node: NimNode): NimNode =
      ##[
            returns last node even if it is
            nested in `if`, `else`, etc. statements
      ]##

      let last = node.last()

      if last.kind notin {nnkIfExpr, nnkIfStmt,
                          nnkElifExpr, nnkElifBranch,
                          nnkElse, nnkElseExpr,
                          nnkCaseStmt, nnkOfBranch,
                          nnkStmtList, nnkStmtListExpr,
                          nnkBlockStmt, nnkBlockExpr}:
            result = last
      else:
            result = last.deepLast()


func callName(call: NimNode): NimNode =
      ## returns name of called func/proc/etc.

      call.expectKind callKinds

      if call[0].kind == nnkIdent:
            result = call[0]
      elif call[0].kind == nnkDotExpr:
            result = call[0][1]


func isCallOf(node: NimNode, f: NimNode): bool =
      f.expectKind routineKinds
      
      if (node.kind in callKinds) and (node.callName == f.name):
            result = true
      else:
            result = false


func normalizedCall(call: NimNode): NimNode =
      ## returns call in `fnName(args)` form

      call.expectKind callKinds

      let name = call.callName

      # if call is `arg.fnName(args)` or `arg.fnName args`
      if call[0].kind == nnkDotExpr:
            result = newCall(name, call[0][0] & call[1..^1])

      # if call is `fnName args` or `fnName(args)`
      elif call[0] == name:
            result = newCall(name, call[1..^1])

      else:
            result = call


func getParams(f: NimNode): seq[Param] =
      f.expectKind routineKinds

      result = @[]

      for param in f.params[1..^1]: # 0th element is return type
            let
                  paramType = param[^2]
                  defaultValue = param[^1]
                  paramNames = param[0 ..< ^2] # we need this because
                                               # param can be `a, b: int`

            for name in paramNames:
                  result.add Param(name: name,
                                   paramType: paramType,
                                   defaultValue: defaultValue)


func names(params: seq[Param]): seq[NimNode] =
      result = @[]
      for param in params:
            result.add param.name


func checkArgs(selfcall, calledFn: NimNode) =
      selfcall.expectKind callKinds
      calledFn.expectKind routineKinds

      if not (selfcall.isCallOf calledFn):
            error "selfcall is not call of passed func"

      let
            name = calledFn.name
            params = calledFn.getParams()
            rawArgs = selfcall[1..^1] # 0th element is fnName
            numberOfParamsWithoutDefaultValue = block:
                  var n = 0
                  for param in params:
                        if param.defaultValue == newEmptyNode():
                              inc n
                  n


      # if there are more arguments passed than parameters
      if rawArgs.len > params.len:
            error("`" & name.repr() & "`" & " got too many args", selfcall)

      # if there are too few arguments passed
      if rawArgs.len < numberOfParamsWithoutDefaultValue:
            error("`" & name.repr() & "`" & " got too few args", selfcall)

      for arg in rawArgs:
            # if arg is in `param=val` form
            if arg.kind == nnkExprEqExpr:
                  let paramName = arg[0]
                  if paramName notin params.names:
                        error("`" & name.repr() & "`" &
                                                " has no param named " &
                                                "`" & paramName.repr() & "`",
                              paramName)


func getArgs(selfcall, calledFn: NimNode): seq[NimNode] =
      ##[
            returns sorted args in `@[1, 2, nil]` form
            (`nil` if param exist, but arg not given)
      ]##

      selfcall.expectKind callKinds
      calledFn.expectKind routineKinds

      if not (selfcall.isCallOf calledFn):
            error "selfcall is not call of passed func"

      selfcall.checkArgs(calledFn)

      let
            params = calledFn.getParams()
            rawArgs = selfcall[1..^1] # 0th element is fnName

      result = newSeq[NimNode](params.len)


      for idx, arg in rawArgs:
            if arg.kind == nnkExprEqExpr:
                  # `param=val` -> `val`
                  let (paramName, value) = (arg[0], arg[1])
                  result[params.names.find(paramName)] = value
            else:
                  result[idx] = arg


func family(node: NimNode): seq[NimNode] =
      ##[
            returns seq with this node, this node's children,
            this node's children's children, etc.
      ]##

      result.add node

      for child in node.children():
            result.add child.family()



func checkShadowing(f: NimNode) =
      f.expectKind routineKinds

      func varNames(varDeclaration: NimNode): seq[NimNode] =
            ##[
                  returns `var`/`let`/`const` names
                  (`@[a]` for `var a: int`; `@[a, b]` for `var a, b: int`)
            ]##

            varDeclaration.expectKind {nnkVarSection,
                                       nnkLetSection,
                                       nnkConstSection}

            result = varDeclaration[0][0 ..< ^2]


      let params = f.getParams()

      for node in f.family():
            if node.kind in {nnkVarSection, nnkLetSection, nnkConstSection}:
                  for name in node.varNames:
                        if name in params.names:
                              error("Params must not be shadowed", name)


func checkParams(f: NimNode) =
      f.expectKind routineKinds
      for param in f.getParams():
            # if paramType is varargs
            if (param.paramType.kind == nnkBracketExpr) and
                                    (param.paramType[0] == ident"varargs"):
                  error("Do not use `varargs`, use `openArray` instead",
                        param.paramType[0])



func optimizeTailRecursionImpl(f: NimNode) =
      f.expectKind routineKinds

      f.checkShadowing()
      f.checkParams()

      let
            body = f.body
            deepLast = body.deepLast()


      #[
            we need tail self-call in `fnName(args)` form,
            so we gonna transform all forms of tail self-call to this,
            and if there is no tail self-call, we just exit this function
      ]#

      #if deepLast is self-call
      if (deepLast.isCallOf f):
            deepLast[] = deepLast.normalizedCall()[]
      # if deepLast is `return {self-call}`
      elif (deepLast.kind == nnkReturnStmt) and (deepLast[0].isCallOf f):
            deepLast[] = deepLast[0].normalizedCall()[]
      # if deepLast is `result = {self-call}`
      elif (deepLast.kind == nnkAsgn and deepLast[0] == ident"result") and
                                                      (deepLast[1].isCallOf f):
            deepLast[] = deepLast[1].normalizedCall()[]
      else:
            warning("function `" & f.name.repr() & "` has no tail-recursion",
                    f)
            return

      let selfcall = deepLast
      

      #[
            transforming function from this form:
            ```
                  func factorial(n: int, acc: int = 1): int =
                        if n <= 1: result = acc
                        else: factorial(n - 1, n * acc)
            ```
            to this form:
            ```
                  func factorial(n: int, acc: int = 1): int =
                        var n = n
                        var acc = acc

                        while true:
                              if n <= 1:
                                    result = acc
                              else:
                                    (n, acc) = (n - 1, n * acc)
                                    continue
                              break
            ```
      ]#


      let
            params = f.getParams()
            args = selfcall.getArgs(f)
            tmpBody = newStmtList()


      #[
            making
            ```
                  var a = a
                  var b = b
            ```
            (`a` and `b` are params)
      ]#

      for param in params:
            let name = param.name

            tmpBody.add(quote do:
                  var `name` = `name`
            ) 


      # `fnName(1, c=3, b=2)` -> `(a, b, c) = (1, 2, 3)`
      let
            vars = nnkTupleConstr.newTree()
            vals = nnkTupleConstr.newTree()

      for idx, arg in args:
            if not arg.isNil():
                  vars.add params[idx].name
                  vals.add arg

      deepLast[] = newStmtList()[]

      if vars.len > 0: deepLast.add(quote do: `vars` = `vals`)
      #-------------------------------------------------


      # if `deepLast` (i.e. `(a, b, c) = (1, 2, 3)`) is last statement,
      # then we don't need `continue` and `break` in the end
      if deepLast == body.last:
            tmpBody.add(quote do:
                  while true:
                        `body`
            )
      else:
            deepLast.add(quote do: continue)
            tmpBody.add(quote do:
                  while true:
                        `body`
                        break
            )

      body[] = tmpBody[]

      when defined(debugTailRecOpt):
            debugEcho f.repr()


macro optimizeTailRecursion*(f: untyped): untyped =
      ##[
            This pragma optimizes tail-recursion, if it exist,
            by transforming recursive function to iterative.
            It can handle `func`s, `proc`s, `method`s and `iterator`s.

            You can compile with `-d:debugTailRecOpt`,
            to print the transformed functions.

            - DO NOT USE `arg.func` (without parentheses) FOR TAIL SELF-CALL,
            BECAUSE IN AST IT HAS NO DIFFERENCE WITH `obj.field`.
            USE `func(arg)`, `func arg`, or `arg.func()` INSTEAD!!!!!!!!!!!!

            - DO NOT SHADOW FUNCTION PARAMETERS,
            THIS MACRO ALREADY SHADOWS THEM!!!!!!!!!!!!

            - DO NOT USE `varargs`,
            I CAN'T CREATE `varargs` VARIABLE!!!!!!!!!!!!

            - CHECK THE ARG TYPES IN THE SELF-CALL YOURSELF,
            BECAUSE IDK HOW TO MAKE FUNCTION FOR IT.
      ]##

      result = f
      result.optimizeTailRecursionImpl()



runnableExamples:
      func factorial(n: int, acc: int = 1): int {.optimizeTailRecursion.} =
            if n <= 1: result = acc
            else: result = factorial(n-1, n*acc)

      iterator items[T](oa: openArray[T]): T {.optimizeTailRecursion.} =
            if oa.len > 0:
                  yield oa[0]
                  oa[1..^1].items()

