import unittest, schemes

test "Using variables":
  defScheme Foo:
    var
      x = 1
      y: int = x + 1
    proc initFoo(): FooObj {.init.}

    behaviors:
      proc init(state: var FooObj) {.init.}

    state Foo1:
      let z: int = y * 2

  var foo = initFoo()
  check:
    foo.x == 1
    foo.y == 2
  
  init(foo)
  check foo.foo1Obj.z == 4

test "Behavior with body":
  defScheme Foo:
    var
      x = 1
      y: int = x + 1
    proc initFoo(): FooObj {.init.}

    behaviors:
      template init(state: var FooObj) {.init.} =
        check y == 2
        initImpl()

    state Foo1:
      let z: int = y * 2

  var foo = initFoo()
  check:
    foo.x == 1
    foo.y == 2
  
  init(foo)
  check foo.foo1Obj.z == 4
