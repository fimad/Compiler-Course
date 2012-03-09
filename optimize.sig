signature OPTIMIZE =
sig
(*.*)

(* optimize from 0 (identity) up to max_level *)
  val optimize : int -> BB.BasicBlockGraph -> BB.BasicBlockGraph
  val max_level : int

end
