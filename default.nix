{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci-matrix ? false,
  override ? {}, ocaml-override ? {}, global-override ? {},
  bundle ? null, job ? null, inNixShell ? null, src ? ./.,
}@args:
let auto = fetchGit {
  url = "https://github.com/4ever2/coq-nix-toolbox.git";
  allRefs = true ;
  # ref = "master";
  rev = import .nix/coq-nix-toolbox.nix;
};
in
import auto ({inherit src;} // args)
