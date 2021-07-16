
# Intuitionistic Epistemic Logic in Coq
This repository contains the Coq development accompanying [Christian Hagemeier's Bachelors Thesis](https://www.ps.uni-saarland.de/~hagemeier/bachelor.php). 

## How to build

To build first install coq and some dependencies using  opam.
First add the official coq repository and create a new opam switch.
```
opam switch create bahagemeier ocaml-base-compiler.4.11.0 
eval $(opam env) # Activate the new switch 
opam repo add coq-released https://coq.inria.fr/opam/released # Add the coq repository
opam install coq.8.13.2 coq-equations # Install coq and coq-equations 
```
Next you can to clone the repository: 
```
git clone --recursive https://github.com/uds-psl/intuitionistic-epistemic-logic.git 
cd intuitionistic-epistemic-logic
```
This should also clone the base-library. 
First you need to compile the base library, for this run
``
make -C external/base-library
``
Afterwards running `make` should compile the project.
If you want to compile the project using multiple threads you can instead run `make -C coq -j 4`.
On my machine a complete build with 4 threads takes about 2.5 minutes, without ca. 4 minutes.

A Coqdoc of this project can be found [here](https://www.ps.uni-saarland.de/~hagemeier/website/toc.html).
## Acknowledgements
* The project uses the uds-psl Base Library.
* We use a permutation solver which is an improved version of [foreverbell's solver](https://github.com/foreverbell/permutation-solver).
* The decidability proof are similar to those by [Hai Dang](https://ps.uni-saarland.de/~dang/ri-lab.php).
* The file `gentree.v` is taken from my ACP Project.

