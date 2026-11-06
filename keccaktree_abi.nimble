# keccaktree nim bindings
mode = ScriptMode.Verbose

packageName   = "keccaktree_abi"
version       = "0.1.0"
author        = "pk910"
description   = "Low-level ABI package for keccaktree, batched keccak256 for merkle trees with a hashtree-compatible API"
license       = "MIT"
installDirs   = @["src", "lib"]
installFiles  = @["keccaktree_abi.nim"]

requires "nim >= 1.6.0"

task test, "Run the keccaktree tests":
  exec "nim c -r -d:release nim/tests/test_keccaktree_abi.nim"
