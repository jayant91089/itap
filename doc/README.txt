Instructions for building ITAP documentation:
1) Go to itap folder inside GAP pkg directory and start gap (either local or global GAP)
2) gap> LoadPackage("itap");
3) gap> LoadPackage("AutoDoc");
4) gap> Read("<path to itap folder>/doc/itap_buildman.g"); # contains functions for building documentation
4) gap> path:="/home/aspitrg3-users/jayant/gap_install/gap4r7/pkg/itap_custom1/doc/"
5) gap> buildman(path);

________________________________________________________________________________________________________

NOTE 1: Function buildman above constructs the manual using AutoDoc as follows:
1) Merge in-code documentation itap_light.gd and examples in doc/examples.txt to create new itap_light.gi file1
2) Running gap> AutoDoc("itap":autosoc:=true);
3) Unmerging examples to restore itap_light.gi

NOTE 2: examples.txt contains examples in Autodoc format. They appear in the same order as the associated functions in
itap_light.gd (it is important to maintain this order). For buildman() to associate the examples with respective functions
add "#!##<funcname>" tag before @BeginExample, when creating new examples.
