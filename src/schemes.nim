import macros, strutils, deques, tables, schemes/util, options

type
  State* = ref object
    name*: string
    kindNode*, objPropName*: NimNode
    isDefault*: bool
    obj*: NimNode
    behaviorImpls*: seq[NimNode]
    members*, schemeMembers*: seq[NimNode]
    flow*: seq[NimNode]
  
  SchemeFlags* = enum
    scfNoneState # adds an initial None state
    scfPublic # export every symbol
    scfRef # define types named the state/scheme name as ref of its object
    scfVar # define types named the state/scheme name as var of its object
    scfDeepRef # make state objects ref too (if ref) and remove their Obj suffix
    scfSpreadShared # put shared fields in every object
    scfSharedObj # separate SchemeSharedObj type for shared fields

  Scheme* = ref object
    name*: string
    flags*: set[SchemeFlags]
    shared*: seq[NimNodeOf[nnkIdentDefs]]
    kindType*: NimNode
    stateEnum*: NimNodeOf[nnkEnumTy]
    stateEnumPrefix*: string
    flow*: seq[tuple[isbehaviorDef: bool, node: NimNode]]
    behaviors*: seq[tuple[name: string, impl, default: NimNode]]
    initBehavior*: Option[int]
    maps*: seq[tuple[name: string, default: NimNode, members: seq[NimNode]]]
    handles*: Table[string, proc(a: NimNode): NimNode]
    handleMacros*: Table[string, NimNode]
    states*: seq[State]
    stateArgumentName*: NimNodeOf[nnkIdent]
    schemeInit*: NimNode
    schemeInitVariable*: NimNode
    sharedDefaultAssignments*: NimNode

var schemeQueue* {.compileTime.} = initDeque[Scheme]()
var currentScheme* {.compileTime.}: Scheme
var schemeTable* {.compileTime.}: Table[string, Scheme]

proc maybeExport(sch: Scheme, idnt: NimNode): NimNode =
  if scfPublic in sch.flags: postfix(idnt, "*") else: idnt

proc addToEnum(sch: Scheme, state: State) =
  if not sch.stateEnum.isNil:
    state.kindNode = ident(sch.stateEnumPrefix & state.name)
    sch.stateEnum.add(state.kindNode)

proc initScheme(sch: Scheme, name: string, flags: set[SchemeFlags], kindType: NimNode) =
  sch.name = name
  if kindType.isNil:
    sch.stateEnum = newTree(nnkEnumTy, newEmptyNode())
    for ch in name:
      if isUpperAscii(ch):
        sch.stateEnumPrefix.add(toLowerAscii(ch))
    sch.stateEnumPrefix.add('s')
    sch.kindType = ident(sch.name & "Kind")
  else:
    sch.kindType = kindType
  if scfNoneState in flags:
    let noneState = State(name: "None", isDefault: true)
    sch.addToEnum(noneState)
    sch.states.add(noneState)
  sch.stateArgumentName = ident"state"

template behavior*(name, body) = discard
template implement*(name, body) = discard
template impl*(name, body) = discard

proc semStateLine(s: State, sch: Scheme, stmt: NimNode) =
  case stmt.kind
  of nnkVarSection, nnkLetSection:
    for v in stmt:
      var typ: NimNode
      let defs = newTree(nnkIdentDefs)
      for i in 0..<v.len-2:
        defs.add(v[i])
      if v[^2].kind != nnkEmpty:
        typ = v[^2]
      if v[^1].kind != nnkEmpty:
        let val = v[^1]
        if typ.isNil:
          typ = quote do: typeof(`val`)
        let setter = newStmtList()
        let objName = s.objPropName
        let stname = sch.stateArgumentName
        for id in defs:
          setter.add(quote do: `stname`.`objName`.`id` = `val`)
        if sch.initBehavior.isSome:
          s.behaviorImpls[sch.initBehavior.get].addOrSetList(setter)
      defs.add(typ)
      defs.add(newEmptyNode()) # objects need this extra empty
      s.obj.add(defs)
  of nnkCommand, nnkCall:
    if stmt[0].kind in {nnkIdent, nnkSym, nnkClosedSymChoice, nnkOpenSymChoice}:
      let first = stmt[0]
      let explicitBehavior = stmt.len == 3 and
        (first.eqIdent"behavior" or first.eqIdent"implement" or first.eqIdent"impl") and
        stmt[1].kind in {nnkStrLit..nnkTripleStrLit, nnkIdent, nnkClosedSymChoice, nnkOpenSymChoice} and
        stmt[2].kind == nnkStmtList
      if explicitBehavior or (stmt.len == 2 and stmt[1].kind == nnkStmtList):
        let behaviorName = if explicitBehavior: $stmt[1] else: $first
        for i, beh in sch.behaviors:
          if beh[0].eqIdent(behaviorName):
            let objName = s.objPropName
            let stname = sch.stateArgumentName
            for v in s.obj:
              for vi in 0..<v.len - 2:
                let a = skipPostfixPragma(v[vi])
                stmt.last.insert(0, newProc(
                  name = a, procType = nnkTemplateDef,
                  params = [ident"auto"],
                  body = (quote do:
                    `stname`.`objName`.`a`),
                  pragmas = newTree(nnkPragma, ident"used")))
            if {scfSpreadShared, scfSharedObj} <= sch.flags:
              for v in sch.shared:
                for vi in 0..<v.len - 2:
                  let a = skipPostfixPragma(v[vi])
                  var ob = stname
                  ob = newDotExpr(ob, objName)
                  ob = newDotExpr(ob, ident"shared") 
                  stmt.last.insert(0, newProc(
                    name = a, procType = nnkTemplateDef,
                    params = [ident"auto"],
                    body = newDotExpr(ob, a),
                    pragmas = newTree(nnkPragma, ident"used")))
            s.behaviorImpls[i].addOrSetList(stmt.last)
            return
        if explicitBehavior:
          error("no such behavior: " & behaviorName, stmt)
      if (let hn = sch.handles.getOrDefault($first, nil); not hn.isNil):
        let handled = (hn)(stmt)
        if handled.kind == nnkStmtList:
          for n in handled:
            semStateLine(s, sch, n)
        else:
          semStateLine(s, sch, handled)
        return
      s.flow.add(stmt)
  of nnkDefer:
    s.behaviorImpls[1].addOrSetList(stmt[0])
  of RoutineNodes:
    if stmt[4].findIdent"member" >= 0:
      for v in s.obj:
        for vi in 0..<v.len - 2:
          let a = skipPostfixPragma(v[vi])
          let stname = sch.stateArgumentName
          stmt.last.insert(0, newProc(
            name = a, procType = nnkTemplateDef,
            params = [ident"auto"],
            body = (quote do:
              `stname`.`a`),
            pragmas = newTree(nnkPragma, ident"used")))
      s.members.add(stmt)
    elif stmt[4].findIdent"schemeMember" >= 0:
      s.schemeMembers.add(stmt)
    else:
      s.flow.add(stmt)
  else: s.flow.add(stmt)

proc semState(sch: Scheme, name: string, kindNode: NimNode, stmtList: NimNode, isDefault = false) =
  let s = State(name: name, kindNode: kindNode, isDefault: isDefault)
  sch.addToEnum(s)
  if stmtList.isNil or stmtList.kind == nnkEmpty:
    sch.states.add(s)
    return
  s.behaviorImpls.newSeq(sch.behaviors.len)
  s.obj = newTree(nnkRecList,
    if scfSpreadShared in sch.flags:
      if scfSharedObj in sch.flags:
        @[newIdentDefs(ident"shared", ident(sch.name & (if scfDeepRef in sch.flags: "Shared" else: "SharedObj")))]
      else:
        sch.shared
    else:
      @[])
  let uncn = uncapitalize(name)
  s.objPropName = ident(if scfDeepRef in sch.flags and {scfRef, scfVar} * sch.flags != {}: uncn else: uncn & "Obj")
  for stmt in stmtList:
    semStateLine(s, sch, stmt)
  sch.states.add(s)

macro addState*(sn) =
  let (isDefault, sn) = if sn.kind in CallNodes and sn[0].eqIdent"default": (true, sn[1]) else: (false, sn)
  let (name, kindNode) = if sn.kind == nnkInfix: ($sn[1], sn[2]) else: ($sn, nil)
  semState(currentScheme, name, kindNode, nil, isDefault)

macro state*(body) =
  let state = currentScheme.states[^1]
  if body.kind == nnkStmtList:
    for b in body: semStateLine(state, currentScheme, b)
  else:
    semStateLine(state, currentScheme, body)

macro state*(sn, body) =
  let (isDefault, sn) = if sn.kind in CallNodes and sn[0].eqIdent"default": (true, sn[1]) else: (false, sn)
  let (name, kindNode) = if sn.kind == nnkInfix: ($sn[1], sn[2]) else: ($sn, nil)
  semState(currentScheme, name, kindNode, body, isDefault)

macro initScheme*(sn; flags: static[set[SchemeFlags]]) =
  let (name, kindType) = if sn.kind == nnkInfix: ($sn[1], sn[2]) else: ($sn, nil)
  let sch = Scheme(flags: flags)
  schemeTable[name] = sch
  schemeQueue.addLast(sch)
  currentScheme = sch
  initScheme(currentScheme, name, flags, kindType)

macro initScheme*(sn) =
  result = getAst(initScheme(sn, {}))

macro shared*(body) =
  case body.kind
  of nnkStmtList:
    result = newStmtList()
    for b in body:
      let ast = getAst(shared(b))
      if not ast.isNil and ast.kind != nnkEmpty:
        result.add(ast)
  of nnkVarSection, nnkLetSection:
    result = newEmptyNode()
    for v in body:
      var typ: NimNode
      let defs = newTree(nnkIdentDefs)
      let last2 = v.len - 2
      let value = v[last2 + 1]
      let valueExists = value.kind != nnkEmpty
      for i in 0..<last2:
        defs.add(v[i])
        currentScheme.sharedDefaultAssignments.addToList(
          newAssignment(
            newDotExpr(
              if scfSpreadShared in currentScheme.flags:
                currentScheme.stateArgumentName
              else:
                currentScheme.schemeInitVariable,
              if scfSharedObj in currentScheme.flags:
                newDotExpr(ident"shared", v[i])
              else:
                v[i]),
            value))
      if v[last2].kind != nnkEmpty:
        typ = v[last2]
      else:
        typ = quote do: typeof(`value`)
      defs.add(typ)
      defs.add(newEmptyNode()) # objects need this to be empty
      currentScheme.shared.add(defs)
      if scfSpreadShared in currentScheme.flags:
        for s in currentScheme.states:
          s.obj.insert(0, defs)
  else:
    result = body

proc semLine(sch: Scheme, st: NimNode) =
  if st.kind in RoutineNodes and st[4].findIdent"behavior" >= 0:
    sch.behaviors.add((skipPostfixPragma(st[0]).strVal, st, nil))
    if st[4].findIdent"init" >= 0:
      sch.initBehavior = some sch.behaviors.high
    sch.flow.add((true, st))
    return
  elif st.kind in {nnkCall, nnkCommand} and st[0].kind in {nnkIdent, nnkSym}:
    if st[0].eqIdent"state":
      let stn = st[1]
      let (name, kindNode) = if stn.kind == nnkInfix: ($stn[1], stn[2]) else: ($stn, nil)
      sch.semState(name, kindNode, if st.len < 3: nil else: st[2])
      return
  sch.flow.add((false, st))

macro behavior*(st) =
  result = newEmptyNode()
  if st.kind == nnkStmtList:
    for s in st:
      discard getAst(behavior(s))
  else:
    currentScheme.behaviors.add((st[0].skipPostfixPragma.strVal, st, nil))
    if st[4].findIdent"init" >= 0:
      currentScheme.initBehavior = some currentScheme.behaviors.high
    currentScheme.flow.add((true, st))

macro behaviorDefault*(name, body) =
  for beh in currentScheme.behaviors.mitems:
    if beh.name == $name:
      beh.default = body

macro inject*(st) =
  result = newEmptyNode()
  if st.kind == nnkStmtList:
    for s in st:
      discard getAst(inject(s))
  else:
    currentScheme.flow.add((false, st))

macro registerHandle*(body) =
  if body.kind == nnkStmtList:
    result = newStmtList()
    for s in body:
      result.add(getAst(registerHandle(s))) 
  elif body.kind == nnkProcDef:
    let nameIdent = skipPostfixPragma(body[0])
    let name = newLit($nameIdent)
    result = quote do:
      `body`
      static:
        currentScheme.handles[`name`] = `nameIdent`
  elif body.kind == nnkTemplateDef:
    let nameIdent = skipPostfixPragma(body[0])
    let name = newLit($nameIdent)
    var params: seq[NimNode]
    for i in 1..<body[3].len:
      for j in 0..body[3][i].len - 3:
        params.add(body[3][i][j])
    let letSection = newNimNode(nnkLetSection)
    let csName = ident("cs")
    for i, p in params:
      letSection.add(newIdentDefs(p, newEmptyNode(), newTree(nnkBracketExpr, csName, newLit(i + 1))))
    let templateBody = body[^1]
    result = quote do:
      static:
        currentScheme.handles[`name`] = proc (`csName`: NimNode): NimNode =
          `letSection`
          result = quote do:
            `templateBody`

macro handle*(sig, body): untyped =
  let nameIdent = sig[0]
  let name = newLit($nameIdent)
  var params: seq[NimNode]
  for i in 1..<sig.len:
    params.add(sig[i])
  let letSection = newNimNode(nnkLetSection)
  let csName = ident("cs")
  for i, p in params:
    letSection.add(newIdentDefs(p, newEmptyNode(), newTree(nnkBracketExpr, csName, newLit(i + 1))))
  let templateBody = body
  result = quote do:
    static:
      currentScheme.handles[`name`] = proc (`csName`: NimNode): NimNode =
        `letSection`
        result = quote do:
          `templateBody`

macro schemeInit*(varName, routine): untyped =
  result = newEmptyNode()
  case routine.kind
  of nnkStmtList:
    for r in routine:
      discard getAst(schemeInit(varName, r))
  of RoutineNodes:
    currentScheme.schemeInit = routine
    currentscheme.schemeInitVariable = varName
  else:
    error("unknown scheme init node kind " & $routine.kind, routine)

template schemeInit*(routine): untyped =
  schemeInit(result, routine)

proc finishScheme(sch: Scheme): NimNode =
  let stateObjName = ident(sch.name & "Obj")
  result = newNimNode(nnkStmtList)
  if not sch.stateEnum.isNil:
    result.add(newTree(nnkTypeSection,
      newTree(nnkTypeDef, sch.maybeExport(sch.kindType), newEmptyNode(), sch.stateEnum)))
  if scfSharedObj in sch.flags:
    let sharedObjTy = newTree(nnkObjectTy, newEmptyNode(), newEmptyNode(), newTree(nnkRecList, sch.shared))
    let ts = newTree(nnkTypeSection,
      newTree(nnkTypeDef,
        sch.maybeExport(ident(sch.name & "SharedObj")),
        newEmptyNode(),
        sharedObjTy))
    if scfRef in sch.flags:
      ts.add(newTree(nnkTypeDef,
        sch.maybeExport(ident(sch.name & "Shared")),
        newEmptyNode(),
        newTree(nnkRefTy, ident(sch.name & "SharedObj"))))
    elif scfVar in sch.flags:
      ts.add(newTree(nnkTypeDef,
        sch.maybeExport(ident(sch.name & "Shared")),
        newEmptyNode(),
        newTree(nnkVarTy, ident(sch.name & "SharedObj"))))
    result.add(ts)
      
  let stateCase = newTree(nnkRecCase, newIdentDefs(ident"kind", sch.kindType))
  let noopBranch = newTree(nnkOfBranch)
  var schemeMembers: seq[NimNode]
  var stateCaseElse: NimNode
  for s in sch.states:
    result.add(s.flow)
    if s.obj.isNil:
      if s.isDefault:
        stateCaseElse = newTree(nnkElse, newNilLit())
      else:
        noopBranch.add(s.kindNode)
    else:
      let obj = newTree(nnkObjectTy, newEmptyNode(), newEmptyNode(), s.obj)
      let id = ident(s.name & "Obj")
      let typedef = newTree(nnkTypeDef, sch.maybeExport(id), newEmptyNode(), obj)
      let ts = newTree(nnkTypeSection, typedef)
      let cmnId = ident(s.name)
      if {scfRef, scfVar} * sch.flags != {}:
        let cmnTypedef = newTree(nnkTypeDef,
          newTree(nnkPragmaExpr, sch.maybeExport(cmnId), newTree(nnkPragma, ident"used")),
          newEmptyNode(),
          newTree(if scfRef in sch.flags: nnkRefTy else: nnkVarTy, id))
        ts.add(cmnTypedef)
      result.add(ts)
      let rl = newTree(nnkRecList,
        newIdentDefs(s.objPropName,
          if {scfDeepRef, scfRef} <= sch.flags: cmnId else: id))
      if s.isDefault:
        if stateCaseElse.isNil:
          stateCaseElse = newTree(nnkElse, rl)
        else:
          error("multiple defaults, first duplicate default: " & s.name)
      else:
        stateCase.add(newTree(nnkOfBranch, s.kindNode, rl))
      for mem in s.members:
        if mem[4].kind != nnkEmpty:
          let behi = mem[4].findIdent"member"
          if behi >= 0:
            mem[4].del(behi)
          if mem[4].len == 0:
            mem[4] = newEmptyNode()
        result.add(mem)
      schemeMembers.add(s.schemeMembers)
    
  if noopBranch.len > 0:
    noopBranch.add(newTree(nnkRecList, newNilLit()))
    stateCase.add(noopBranch)
  
  if not stateCaseElse.isNil:
    stateCase.add(stateCaseElse)
  
  let schemeObj = newTree(nnkRecList,
    if scfSpreadShared in sch.flags: @[]
    elif scfSharedObj in sch.flags: @[newIdentDefs(
      ident"shared", ident(sch.name & (if scfDeepRef in sch.flags: "Shared" else: "SharedObj")))]
    else: sch.shared)
  schemeObj.add(stateCase)
  let objTree = newTree(nnkTypeSection,
    newTree(nnkTypeDef, sch.maybeExport(stateObjName), newEmptyNode(),
      newTree(nnkObjectTy, newEmptyNode(), newEmptyNode(),
        schemeObj)))
  if {scfRef, scfVar} * sch.flags != {}:
    objTree.add(newTree(nnkTypeDef,
      sch.maybeExport(ident(sch.name)),
      newEmptyNode(),
      newTree(if scfRef in sch.flags: nnkRefTy else: nnkVarTy, stateObjName)))
  result.add(objTree)

  for m in sch.maps:
    discard#let (name, default, members) = m


  for schMem in schemeMembers:
    if schMem[4].kind != nnkEmpty:
      let behi = schMem[4].findIdent"schemeMember"
      if behi >= 0:
        schMem[4].del(behi)
      if schMem[4].len == 0:
        schMem[4] = newEmptyNode()
    result.add(schMem)
  
  var assignedSchemeDefaults = false
  var behIndex = 0
  for isBeh, f in sch.flow.items:
    if isBeh:
      let caseBranch = newTree(nnkCaseStmt, newDotExpr(sch.stateArgumentName, ident"kind"))
      let defaults = newTree(nnkOfBranch)
      var elseBranch: NimNode
      for s in sch.states:
        if behIndex < s.behaviorImpls.len and not s.behaviorImpls[behIndex].isNil:
          if s.isDefault:
            elseBranch = newTree(nnkElse, s.behaviorImpls[behIndex])
          else:
            caseBranch.add(newTree(nnkOfBranch, s.kindNode, s.behaviorImpls[behIndex]))
        elif s.isDefault:
          elseBranch = newTree(nnkElse,
            if sch.behaviors[behIndex].default.isNil:
              newTree(nnkDiscardStmt, newEmptyNode())
            else:
              sch.behaviors[behIndex].default)
        else:
          defaults.add(s.kindNode)
      if defaults.len > 0:
        defaults.add(
          if sch.behaviors[behIndex].default.isNil:
            newTree(nnkDiscardStmt, newEmptyNode())
          else:
            sch.behaviors[behIndex].default)
        caseBranch.add(defaults)
      if not elseBranch.isNil:
        caseBranch.add(elseBranch)
      var empty = false
      if f[6].kind == nnkEmpty: empty = true; f[6] = newStmtList()
      elif f[6].kind != nnkStmtList: f[6] = newStmtList(f[6])
      else: empty = f[6].len == 0
      if scfSpreadShared notin sch.flags:
        for v in sch.shared:
          for vi in 0..<v.len - 2:
            let a = skipPostfixPragma(v[vi])
            var ob = sch.stateArgumentName
            if scfSharedObj in sch.flags:
              ob = newDotExpr(ob, ident"shared") 
            f[6].insert(0, newProc(
              name = a, procType = nnkTemplateDef,
              params = [ident"auto"],
              body = newDotExpr(ob, a),
              pragmas = newTree(nnkPragma, ident"used")))
      var pragmas = f[4]
      var isInit = false
      if pragmas.kind != nnkEmpty:
        if (let behi = pragmas.findIdent"behavior"; behi) >= 0:
          pragmas.del(behi)
        if (let ini = pragmas.findIdent"init"; ini) >= 0:
          pragmas.del(ini)
          isInit = true
          if scfSpreadShared in sch.flags:
            f[6].insert(0, sch.sharedDefaultAssignments)
            assignedSchemeDefaults = true
        if pragmas.len == 0:
          pragmas = newEmptyNode()
      f[4] = pragmas
      if empty:
        f[6].add(newStmtList(caseBranch))
      else:
        var newPragmas = copyNimTree(pragmas)
        if newPragmas.kind != nnkEmpty:
          newPragmas.add(ident"gensym")
        else:
          newPragmas = newTree(nnkPragma, ident"gensym")
        #var tys = @[stateObjName]
        #if {scfVar, scfRef} * sch.flags != {}:
        #  tys.add(ident(sch.name))
        #for ty in tys:
        f[6].insert(0, newProc(
          name = ident($f[0] & "Impl"),
          procType = nnkTemplateDef,
          params = [ident"untyped"],#, newIdentDefs(ident"_", newTree(nnkBracketExpr, ident"typedesc", ty))],
          body = caseBranch,
          pragmas = newPragmas
        ))
      inc behIndex
    result.add(f)
  
  if not sch.schemeInit.isNil:
    let init = copy sch.schemeInit
    if init[6].isNil or init[6].kind == nnkEmpty: init[6] = newStmtList()
    elif init[6].kind != nnkStmtList: init[6] = newStmtList(init[6])
    if scfSpreadShared notin sch.flags:
      init[6].insert(0, sch.sharedDefaultAssignments)
      assignedSchemeDefaults = true
    result.add(init)
  
  if not sch.sharedDefaultAssignments.isNil and not assignedSchemeDefaults:
    warning("shared fields with default values never initialized", sch.sharedDefaultAssignments)
  #echo result.repr

macro endScheme*() =
  result = finishScheme(currentScheme)
  if schemeQueue.peekLast == currentScheme:
    schemeQueue.shrink(fromLast = 1)
  if schemeQueue.len > 0:
    currentScheme = schemeQueue.peekLast

macro defScheme*(sn, body): untyped =
  let (name, kindType) = if sn.kind == nnkInfix: ($sn[1], sn[2]) else: ($sn, nil)
  let sch = Scheme()
  initScheme(sch, name, {}, kindType)
  for st in body:
    semLine(sch, st)
  result = finishScheme(sch)