# OpenJML-Quantifiers

JML Reference Guide: https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_toc.html

## OpenJML

To run our version of OpenJML:

First set up [the development enviroment](https://github.com/OpenJML/OpenJML/wiki/OpenJML-Development-Environment-Setup):

```bash
mkdir OpenJML && cd OpenJML
git clone -b master-module https://github.com/OpenJML-SeniorDesign/OpenJML.git
git clone -b master-module https://github.com/OpenJML/Specs.git
git clone -b master https://github.com/OpenJML/Solvers.git
git clone -b master https://github.com/OpenJML/JMLAnnotations.git
```

Then, do a [build](https://github.com/OpenJML/OpenJML/wiki/Building-OpenJML):

## Building JDK
If you need any help building the JDK refer to these links:
https://openjdk.java.net/groups/build/doc/building.html
https://metebalci.com/blog/custom-openjdk-10-builds-on-ubuntu-16.04/

```bash
cd OpenJML/OpenJDKModule
bash ./configure
# Use the line below for WSL
# bash ./configure --with-boot-jdk=/usr/lib/jvm/java-16-openjdk-amd64 --disable-warnings-as-errors --build=x86_64-unknown-linux-gnu --host=x86_64-unknown-linux-gnu
make openjml
make release
```

Then, to use OpenJML

```bash
./OpenJML/OpenJDKModule/release-temp/openjml -esc --prover=z3_4_7 <filename>
```

## SMT Solving

Z3 Solver:

-   https://github.com/Z3Prover/z3/releases
-   https://pypi.org/project/z3-solver/

Online Z3 tools:

-   https://jfmc.github.io/z3-play/
-   https://compsys-tools.ens-lyon.fr/z3/

Resources:

-   https://ericpony.github.io/z3py-tutorial/guide-examples.htm
-   https://github.com/ericpony/z3py-tutorial
-   https://theory.stanford.edu/~nikolaj/programmingz3.html

## Quantifier Resources:

-   Leino and Monahan 2009: https://dl.acm.org/doi/10.1145/1529282.1529411
-   Axiom debugging: https://github.com/viperproject/axiom-profiler
-   Sketch Sharp tool: https://github.com/hesam/SketchSharp
-   Boogie tool: https://github.com/boogie-org/boogie
