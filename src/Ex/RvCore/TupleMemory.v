Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Datatypes.HList coqutil.Byte.

Local Open Scope Z_scope.

(* The case study uses the tuple memory interface from riscv-coq before
   commit 2d662a3. These definitions preserve its byte order, address stepping,
   and failure on unmapped addresses for the machine and its proofs. *)
Section MemAccess.
  Context {width: Z} {word: word width} {mem: map.map word byte}.

  Definition footprint (a: word) (sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes (sz: nat) (m: mem) (a: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint a sz).

  Definition unchecked_store_bytes (sz: nat) (m: mem) (a: word)
    (bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  Definition store_bytes (sz: nat) (m: mem) (a: word)
    (bs: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a bs)
    | None => None
    end.
End MemAccess.
