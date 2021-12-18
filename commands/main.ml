open Cmdliner

let default_cmd =
  let doc = "An implementation of the lambdaPi calculus modulo rewriting" in
  let sdocs = Manpage.s_common_options in
  let exits = Term.default_exits in
  let man =
    [
      `S Manpage.s_description;
      `P
        "Dedukti is a set of tools to interact with files written in the \
         Dedukti language.";
    ]
  in
  ( Term.(ret (const (fun _ -> `Help (`Pager, None)) $ Config.t)),
    Term.info "dedukti" ~version:"%%VERSION%%" ~doc ~sdocs ~exits ~man )

let cmds = [Dkcheck.cmd; Dkdep.cmd; Dkpretty.cmd]

let () = Term.(exit @@ eval_choice default_cmd cmds)
