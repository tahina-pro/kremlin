module RenameLet

module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module I32 = FStar.Int32
module B = LowStar.Buffer

let test () : HST.Stack C.exit_code (fun _ -> True) (fun _ _ _ -> True) = C.EXIT_SUCCESS

let main
  (argc: I32.t)
  (argv: B.buffer (B.buffer C.char))
: HST.Stack C.exit_code
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
= [@rename_let "essai"]
  let x = test () in
  x
