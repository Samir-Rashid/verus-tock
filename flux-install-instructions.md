# List of commands to run to get Flux running on Tock
Unfortunately, you can't run this stuff without polluting your computer with
hard coded paths. It wasn't worth my time to finish figuring out how to
package liquid-fixpoint, fix Flux hard coded paths, and (separately) to
package Verus.

I keep all the relevant repos in one folder. You will eventually run into
bugs in the dependencies, so it helps to keep a local copy you can modify.

```
vtock/
├── flux
├── liquid-fixpoint
└── tock
```

## liquid fixpoint
- https://github.com/ucsd-progsys/liquid-fixpoint
cd liquid-fixpoint && git checkout develop && git pull 
nix-shell -p stack z3
stack install

## flux
- https://github.com/flux-rs/flux
- need /home/$USER/.local/bin to be on path
PATH=/home/mod/.local/bin:$PATH
cd flux && nix-shell -p rustup z3 && cargo xtask install

## flux vscode extension
You will want the flux extension, which is in `tools/vscode` of the flux repo
I have this `shell.nix` sitting in this folder. Looks like I copied it from elsewhere.
Refer to the documentation in this folder for exact instructions.
```
{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell {
  buildInputs = with pkgs; [
    nodejs
    yarn
    esbuild
    vsce # used to publish the extension
  ];
  shellHook = ''
    # These lines are only needed for the initial extension bootstrap `yo code`

    # mkdir -p ./.npm-global
    # npm config set prefix '/home/samir/Documents/github/pytrail/.npm-global'
    # export PATH=/home/samir/Documents/github/pytrail/.npm-global/bin:$PATH

    npm install
    echo "Use 'npm run debug'"
  '';
}
```
I also have this diff in `package-lock.json`. Unsure if necessary.
```
"vscode": "^1.92.0"
```

## Now you should be able to verify vtock.
- https://github.com/PLSysSec/tock
I recommend making a dummy folder in arch/ where you can test using `cargo flux`.

## Quirks:
- You may need to pin your version of verus (ex: z3_4_12)
- I keep an empty "playground.rs" file in the Flux repo to test verifying small functions and make bug reproducers.
  You can run it directly and get all the snazzy output with `FLUX_DUMP_CHECKER_TRACE=1 FLUX_DUMP_CONSTRAINT=1 FLUX_DUMP_MIR=1 cargo xtask run playground.rs`
