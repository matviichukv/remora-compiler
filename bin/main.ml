open! Base
open Remora

type outputType =
  | OutputDir of string
  | OutputFile of string
  | OutputStdout

let processErrors (errors : (Source.t option, string) Source.annotate NeList.t)
  : (_, Error.t) Result.t
  =
  errors
  |> NeList.map ~f:(fun error ->
    match error.source with
    | Some { start; finish } ->
      let showPos (pos : Lexing.position) =
        [%string "%{pos.pos_lnum#Int}:%{(pos.pos_cnum - pos.pos_bol)#Int}"]
      in
      let errorMsg =
        [%string "Error (%{showPos start} - %{showPos finish}): %{error.elem}"]
      in
      Error.of_string errorMsg
    | None -> Error.of_string [%string "Error: %{error.elem}"])
  |> NeList.to_list
  |> Error.of_list
  |> Result.Error
;;

let writeCompiledProgramToFile file program =
  Stdlib.Out_channel.with_open_gen [] 0o644 file (fun file ->
    Stdlib.Out_channel.output_string file program;
    Stdlib.Out_channel.flush file;
    Ok ())
;;

let writeCompiledProgramToDirectory dir program =
  let open Result.Let_syntax in
  let exists = Stdlib.Sys.file_exists dir in
  let%bind () =
    if not exists
    then (
      Stdlib.Sys.mkdir dir 0o744;
      Ok ())
    else if not (Stdlib.Sys.is_directory dir)
    then Error (Error.of_string "Tried to write a directory to a file")
    else Ok () (* directory exists *)
  in
  let flags = [ Open_creat; Open_trunc; Open_text; Open_wronly ] in
  let mainFileName = "main.cu" in
  let mainFile = Stdlib.Filename.concat dir mainFileName in
  let%bind () =
    Stdlib.Out_channel.with_open_gen flags 0o644 mainFile (fun file ->
      Stdlib.Out_channel.output_string file program;
      Stdlib.Out_channel.flush file;
      Ok ())
  in
  let cmakeFile = Stdlib.Filename.concat dir "CMakeLists.txt" in
  let%bind () =
    Stdlib.Out_channel.with_open_gen flags 0o644 cmakeFile (fun file ->
      Stdlib.Out_channel.output_string
        file
        (Compiler.Default.cmakeFileContents mainFileName);
      Stdlib.Out_channel.flush file;
      Ok ())
  in
  Ok ()
;;

let dependencies = "HighFive (for H5 file IO), stb_image (for reading images)"

let command =
  Command.basic_or_error
    ~summary:"Compile a Remora program into a C++ CUDA program (.cu extension)"
    ~readme:(fun () ->
      [%string "Resulting programs needs to be linked to dependencies: %{dependencies}. "])
    (let open Command.Param in
     let open Command.Let_syntax in
     let outputFile =
       map
         (flag
            ~doc:
              [%string
                "Output the resulting C++ CUDA program into a file. You would need to \
                 manually link it to dependencies in order to compile it. \
                 %{dependencies}"]
            "-o"
            (optional string))
         ~f:(Option.map ~f:(fun v -> OutputFile v))
     in
     let outputDir =
       map
         (flag
            ~doc:
              "Output the resulting C++ CUDA program into a directory, with a \
               CMakeLists.txt file and program in main.cu. CMakeLists.txt would have \
               everything to download and link dependencies automatically"
            "-d"
            (optional string))
         ~f:(Option.map ~f:(fun v -> OutputDir v))
     in
     let%map output =
       choose_one [ outputFile; outputDir ] ~if_nothing_chosen:(Default_to OutputStdout)
     and input = anon (maybe ("<input file>" %: string)) in
     let inputChannel =
       match input with
       | None -> Stdio.stdin
       | Some filename -> Stdio.In_channel.create filename
     in
     let program = Stdio.In_channel.input_all inputChannel in
     let result = Compiler.Default.compileStringToString program in
     fun () ->
       match result with
       | MOk outProgram ->
         (match output with
          | OutputDir path -> writeCompiledProgramToDirectory path outProgram
          | OutputFile path -> writeCompiledProgramToFile path outProgram
          | OutputStdout ->
            Stdio.print_endline outProgram;
            Ok ())
       | Errors errors -> processErrors errors)
;;

let () = Command_unix.run ?version:(Some "0.1") command
(* let () = *)
(*   let args = Sys.get_argv () in *)
(*   let channel = *)
(*     match Array.to_list args with *)
(*     | _ :: filename :: _ -> Stdio.In_channel.create filename *)
(*     | _ -> Stdio.stdin *)
(*   in *)
(*   let program = Stdio.In_channel.input_all channel in *)
(*   match Compiler.Default.compileStringToString program with *)
(*   | MOk outProgram -> Stdio.print_endline outProgram *)
(*   | Errors errors -> *)
(*     NeList.iter errors ~f:(fun { elem = error; source } -> *)
(*       match source with *)
(*       | Some { start; finish } -> *)
(*         let showPos (pos : Lexing.position) = *)
(*           [%string "%{pos.pos_lnum#Int}:%{(pos.pos_cnum - pos.pos_bol)#Int}"] *)
(*         in *)
(*         Stdio.prerr_endline *)
(*           [%string "Error (%{showPos start} - %{showPos finish}): %{error}"] *)
(*       | None -> Stdio.prerr_endline [%string "Error: %{error}"]); *)
(*     Stdlib.exit 1 *)
(* ;; *)
