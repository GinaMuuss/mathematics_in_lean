{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =                                                                                             
    {                        
      self,                 
      nixpkgs,      
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:                       
      let                                 
        pkgs = import nixpkgs {
          inherit system;                  
          config.allowUnfree = true;
        };               
                                                    
        lean-packages = with pkgs; [
          elan
        ];                 
                                                    
        dev-packages = with pkgs; [         
          (vscode-with-extensions.override {
            vscode = vscodium;
            vscodeExtensions = with vscode-extensions; [
            ] ++ pkgs.vscode-utils.extensionsFromVscodeMarketplace [
              {
                name = "lean4";
                publisher = "leanprover";
                version = "0.0.221";
                sha256 = "OoDM9PuhQBRln41OHdVbI8EcXaqIQPArnqgFt+63aJg=";
              }
              {
                name = "even-better-toml";
                publisher = "tamasfe";
                version = "0.21.2";
                sha256 = "IbjWavQoXu4x4hpEkvkhqzbf/NhZpn8RFdKTAnRlCAg=";
              }
            ];
          })
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            lean-packages
            dev-packages
          ];
        };
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "leanenv";
          version = "0.1.0";
          src = ./.;

        };
      }
    );

}
