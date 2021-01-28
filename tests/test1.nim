import unittest

import schemes

test "instructions":
  initScheme Instruction, {scfNoneState}

  proc operate(state: InstructionObj, value: var int) {.inline, behavior.}

  state Add:
    let x: int

    operate:
      inc value, x
  
  state Negate:
    operate:
      value = -value
  
  state Multiply:
    let x: int

    operate:
      value *= x
  
  state Divide:
    let x: int

    operate:
      value = value div x
  
  endScheme()
  
  proc parseInstructions(s: string): seq[InstructionObj] =
    var i = 0
    while i < s.len:
      result.add(
        case s[i]
        of '+': InstructionObj(kind: isAdd, addObj: AddObj(x: int s[(inc i; i)]))
        of '-': InstructionObj(kind: isNegate)
        of '*': InstructionObj(kind: isMultiply, multiplyObj: MultiplyObj(x: int s[(inc i; i)]))
        of '/': InstructionObj(kind: isDivide, divideObj: DivideObj(x: int s[(inc i; i)]))
        else: InstructionObj(kind: isNone))
      inc i
  
  proc runInstructions(s: seq[InstructionObj], initial: int): int =
    result = initial
    for i in s: i.operate(result)

  check runInstructions(parseInstructions("+\3-+\2-*\2*\2*\3/\5"), 0) == 2
