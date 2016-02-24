#############################################################################
##
##                                                      itap package
##
##  Copyright 2015,           Jayant Apte and John Walsh, Drexel University
##
##  The .gd file containing global function declarations and the documentation
##  of the itap package. The documentation is written using the AutoDoc Package.
##
##
#############################################################################



#! @Chapter Introduction
#! ITAP stands for Information Theoretic Achievability Prover. So basically, it
#! is intended for coming up with achievability proofs using a computer.
#! As of now, it supports the following:
#! * Achievability proofs of multi-source network coding using
#!   vector-linear codes: answer questions like 'Is this rate
#!   vector achievable using a vector linear code over the given finite field?'.
#!   If the answer is `yes` it also returns the vector linear code it found as
#!   a certificate of achievability. Otherwise, it just says 'no'.
#! * Achievability proofs with multi-linear secret sharing schemes: answer questions
#!   'Is there a multi-linear secret sharing scheme over $GF(q)$ for this access structure?'
#! * Representability test for integer polymatroids over a given finite
#!   field: answer questions like `Is the integer polymatroid associated with this
#!   rank vector linear over $GF(q)$?
#! * Achievable Rate Region Computation: For a network coding instance, what is the rate region achievable
#!   using linear codes with maximum message size $k$ and maximum code dimension $d$?
#! Above questions are very similar to each other, in that, we are looking for
#! linear representations of integer polymatroids satisfying certain properties
#! (i.e. network coding constraints, access structure or having a specified rank vecor respectively).
#! In its most general form an achievability prover is a computer program that able to answer
#! if there exists a joint distribution satisfying certain constraints on
#! entropy function. It is not known how to design such a computer program, as it is closely related to
#! the characterization of the entropy function. ITAP tries
#! answering this existential question in a much restricted sense, i.e. with respect to the joint distributions arising
#! from vector linear codes aka integer linear polymatroids.
#! The main algorithm underlying ITAP is called Leiterspiel or the algorithm
#! of snakes and ladders. See <Cite Key="betten2006error"/> for details. For answering the first question
#! in the above list, one can also use the algebraic formulation of Koetter and Medard <Cite Key="koetteralgebraic03"/>
#! or its refinements such as the path gain formulation of Subramanian and Thangaraj <Cite Key="subrapathgain10"/>.
#! These formulations lead to a system of polynomial equations over a finite field and allows one to use Groebner
#! basis computation algorithms to answer question 1. ITAP currently supports such computation using Singular
#! <Cite Key="DGPS"/> via the GAP interface to Singular<Cite Key="singulargap"/>.
#! #! @Chapter Installation
#! ITAP requires GAP interface to singular <Cite Key="singulargap"/> which is another GAP package.
#! Nowadays, it comes bundled with GAP 4.7+. If your gap installation doesn't have this package
#! you can follow the instructions in <Cite Key="singulargap"/> to install it.
#! To get the newest version of ITAP, download the .zip archive from <URL>https://github.com/jayant91089/itap</URL>
#! and unpack it using
#! $$\texttt{unzip itap-x.zip}$$
#! Do this preferably inside the $pkg$ subdirectory
#! of your GAP 4 installation. It creates a subdirectory called $itap$.
#! This completes the installation of the package. If you do not know the whereabouts of the $pkg$ subdirectory, invoke the following in GAP:
#! @BeginCode pkg
GAPInfo.("RootPaths");
 #! @EndCode
#! @InsertCode pkg
#! Look for pkg directory inside any of the paths returned.
#! One can then start using ITAP by invoking
#! @BeginCode Read
 LoadPackage( "itap");
 #! @EndCode
#! $$gap>$$
#! @InsertCode Read
#! from within GAP. This would automatically load the GAP interface to singular, so you don't have to load it seperately.
#! @BeginCode pkg
GAPInfo.("RootPaths");
 #! @EndCode
#! @InsertCode pkg
#! Look for pkg directory inside any of the paths returned.
#! One can then start using ITAP by invoking
#! @BeginCode Read
 LoadPackage( "itap");
 #! @EndCode
#! $$gap>$$
#! @InsertCode Read
#! from within GAP. This would automatically load the GAP interface to singular, so you don't have to load it seperately.
#! @BeginCode GF
q:=4;;
F:= GF(q);; # here q must be a prime power
#! @EndCode

#! @Chapter Usage
#! @Section Available functions
#!  In this section we shall look at the functions provided by ITAP.
#! @Description
#! This function checks if there is a linear representation of an integer polymatroid rank vector.
#! It accepts following arguments:
#! * $rankvec$ - A list of integers specifying a polymatroid rank vector
#! * $nvars$ - Number of ground set elements
#! * $F$ - The finite field over which we wish to find a linear representation. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $optargs$ is a list of optional arguments $[lazy,..]$ where
#!   * $lazy$ disables lazy evaluation of transporter maps if set to $false$, which is enabled by default
#!       in GAP.
#! Returns a list $[true,code]$ if there exists such a representation and $code$ is the vector linear code over $GF(q)$
#! Returns a list $[false]$ otherwise, indicating that no such representation exists
#! @Returns A list
#! @Arguments rankvec,nvars,F,optargs
DeclareGlobalFunction("proverep");
#! @Description
#!  This function checks if there is a vector linear code achieving the
#!  rate vector $rvec$ for the network coding instance $ncinstance$. Uses enumerative generation methods
#! to syetematically search for the code with desired properties.
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! * $rvec$ - A list of $nvars$ integers specifying a rate vector
#! * $ F$ is the finite field over which we wish to find the vector linear code. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $optargs$ is a list of optional arguments $[lazy,..]$ where $lazy$ disables lazy evaluation
#!   of transporter maps if set to $false$, which is enabled by default.
#! Returns a list $[true,code]$ if there exists such a representation and $code$ is the vector linear code over $GF(q)$
#! Returns a list $[false]$ otherwise, indicating that no such code exists
#! @Returns A list
#! @Arguments ncinstance,rvec,F,optargs
DeclareGlobalFunction("proverate");
#! @Description
#!  This function computes the all rate vectors achievable via vector linear CodeString
#! over the specified fiite field for the network coding instance $ncinstance$. Uses enumerative generation methods
#! to syetematically search for codes with desired properties.
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! * $k$ - Maximum number of symbols per message
#! * $ F$ is the finite field over which we wish to find the vector linear codes. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $optargs$ is a list of optional arguments $[opt_dmax,..]$ where $opt_dmax$ specifies an upper bound on the
#!   dimension of linear codes (alternatively, the rank of underlying polymatroid) to search. By default this is equal to $nsrc*k$, which
#!   may sometimes be unnecessary, and a lower value might suffice.
#! Returns a list $[rays,codes]$ where $rays$ is a list of all achievable rate vectors and codes is a list of linear codes.
#! @Returns A list
#! @Arguments ncinstance,k,F,optargs
DeclareGlobalFunction("proveregion");
#! @Description
#!  This function checks if there is a vector linear code achieving the
#!  rate vector $rvec$ for the network coding instance $ncinstance$. Uses GAP interface to
#! $Singular$ to find Groebner basis of the system of polynomial equations given by the path gain algebraic
#! construction of Subramanian and Thangraj <Cite Key="subrapathgain10"/> .
#! It accepts following arguments:
#! * $ncinstance$ is a list  $[cons,nsrc,nvars]$ containing 3 elements:
#!   * $cons$ is a list of network coding constraints.
#!   * $nsrc$ is the number of sources.
#!   * $nvars$ is the number of random variables associated with the network.
#! * $rvec$ - A list of $nvars$ integers specifying a rate vector
#! * $ F$ is the finite field over which we wish to find the vector linear code. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $optargs$ is a list of optional arguments $[lazy,..]$ where $lazy$ disables lazy evaluation
#!   of transporter maps if set to $false$, which is enabled by default.
#! Returns a list $[true,code]$ if there exists such a representation where $code$ is the vector linear code over $GF(q)$.
#! Returns a list $[false]$ otherwise, indicating that no such code exists
#! @Returns A list
#! @Arguments ncinstance,rvec,F,optargs
DeclareGlobalFunction("proverate_groebner");
#! $\textbf{NOTE:}$ Certain naming convensions are followed while defining network coding instances. The source messages are labeled with
#! $[1...nsrc]$ while rest of the messages are labeled $[nsrc...nvars]$. Furthermore, the list $cons$ includes
#! all network constraints except source independence. This constraint is implied with the labeling i.e. ITAP
#! enforces it  by default for the messages labeled $[1...nsrc]$. See next section for usage examples.

#! @Description
#! This function checks if there is a multi-linear secret sharing scheme with secret and share
#! sizes given by $svec$ and the access structure $Asets$ with one dealer and
#! $nvars-1$ parties.
#! It accepts following arguments:
#! * $Asets$ - A list of authorized sets each specified as a subset of $[nvars-1]$
#! * $nvars$ - Number of participants (including one dealer)
#! * $svec$ - vector of integer share sizes understood as number of $\mathbb{F}_q$ symbols, with index 1 giving secret size and index $i,i\in \{2,...,nvars\}$ specifying share sizes of different parties
#! * $F$ - The finite field over which we wish to find a multi-linear scheme. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $optargs$ is a list of optional arguments $[lazy,..]$ where
#!   * $lazy$ disables lazy evaluation of transporter maps if set to $false$, which is enabled by default
#!       in GAP.
#! Returns a list $[true,code]$ if there exists such a scheme where $code$ is the vector linear code over $GF(q)$.
#! Returns a list $[false]$ otherwise, indicating that no such scheme exists.
#! @Returns A list
#! @Arguments Asets,nvars,svec,F,optargs
DeclareGlobalFunction("provess");
#! $\textbf{NOTE:}$ No input checking is performed to verify if input $Asets$ follows labeling convensions. The map returned
#! with a linear scheme is a map $f:[nvars]\rightarrow [nvars]$ with dealer associated with label 1 and parties
#! associated with labels $\{2,...,nvars\}$. See next section for usage examples.

#! @Description
#!  Displays a network code (or an integer polymatroid).
#! It accepts 1 argument:
#! * $code$ - A list $[s,map]$ containing 2 elements:
#!   * $s$ - A list of subspaces where is subspace is itself a list of basis vectors
#!   * $map$ - A GAP record mapping subspaces in $s$ to network messages or to polymatroid ground set elements
#! Returns nothing
#! @Returns nothing
#! @Arguments code
DeclareGlobalFunction("DisplayCode");

#! @Section A catalog of examples
#! $\texttt{itap}$ comes equipped with a catalog of examples, which contains well-known network coding instances and integer polymatroids.
#! This catalog is intended to be of help to the user for getting started with using $\texttt{itap}$. Most of the network coding instances
#! in this catalog can be found in <Cite Key="YeungBook"/> and <Cite Key="DFZMatroidNetworks"/>. Some of the integer polymatroids in the catalog
#! are taken from <URL>http://code.ucsd.edu/zeger/linrank/</URL>. These polymatroids correspond to the extreme rays of the cone of linear rank
#! inequalities in 5 variables, found by Dougherty, Freiling and Zeger. See <Cite Key="DFZ2009Ineqfor5var"/> for details.
#! @Description
#!  Returns the Fano instance.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("FanoNet");


#! @Description
#!  Returns the NonFano instance.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("NonFanoNet");

#! @Description
#!  Returns the Vamos instance.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("VamosNet");


#! @Description
#!  Returns the instance associated with uniform matroid $U^2_k$.
#! It accepts one argument $\texttt{k}$ specifying the size of uniform matroid.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("U2kNet");


#! @Description
#!  Returns the Butterfly instance.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("ButterflyNet");


#! @Description
#!  Returns the extreme rays of cone formed by linear rank inequalities in 5 variables.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("Subspace5");

#! @Description
#!  Returns the access structure associated with secret sharing scheme of Benaloah and Leichter that
#! was used to show that share sizes can be larger than secret size. See <Cite Key="Benaloh90"/> for details.
#! It accepts no arguments.
#! Returns a list.
#! @Returns A list of lists specifing authorized subsets of $\{1,2,3,4\}$
#! @Arguments
DeclareGlobalFunction("BenalohLeichter");

#! @Description
#!  Returns the access structure associated with Shamir's $(k,n)$ threshold scheme.
#!  See <Cite Key="Shamirhowto79"/> for details.
#! It accepts following arguments:
#! * $\texttt{n}$ - number of shares
#! * $\texttt{k}$ - threshold
#! @Returns A list of lists specifing authorized subsets of $[n]]$
#! @Arguments
DeclareGlobalFunction("Threshold");

#! @Description
#!  Returns a general hyperedge network obtained via enumeration of network coding instances.
#!  See <Cite Key="lihyper15"/> for details.
#! It accepts no arguments.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("HyperedgeNet1");

#! @Description
#!  Returns a general hyperedge network obtained via enumeration of network coding instances.
#!  See <Cite Key="lihyper15"/> for details.
#! It accepts no arguments.
#! @Returns A list
#! @Arguments
DeclareGlobalFunction("HyperedgeNet2");

DeclareGlobalFunction("MSdecomp");
DeclareGlobalFunction("Group2eqlist");
DeclareGlobalFunction("TranSub");
DeclareGlobalFunction("partSub");

DeclareGlobalFunction("testcons_ss");
DeclareGlobalFunction("IsAuthSet");
DeclareGlobalFunction("findsss");
DeclareGlobalFunction("set2int");
DeclareGlobalFunction("AppCns");
DeclareGlobalFunction("inv_pcode");
DeclareGlobalFunction("RecSetwise");
DeclareGlobalFunction("SubRankMat");
DeclareGlobalFunction("SubRankMat_vec");
DeclareGlobalFunction("merge_veclist");
DeclareGlobalFunction("RecNamesInt");
DeclareGlobalFunction("codedegrees");
DeclareGlobalFunction("codedegrees_vec");
DeclareGlobalFunction("extend_pcodes");
DeclareGlobalFunction("disp_scalar_pcode");
DeclareGlobalFunction("disp_subsparr");
DeclareGlobalFunction("extend_pcodes_vec_prover");
DeclareGlobalFunction("testcons_withrankvec");
DeclareGlobalFunction("certsearch_rep_prover_verbose");
DeclareGlobalFunction("certsearch_rep_prover");
DeclareGlobalFunction("extend_pcodes_rep_prover");
DeclareGlobalFunction("parallel_extensions");
DeclareGlobalFunction("parallel_extensions_vec");
DeclareGlobalFunction("zerovec");
DeclareGlobalFunction("nonsimple_extensions_vec");
DeclareGlobalFunction("rec2perm");
DeclareGlobalFunction("rec_iso");
DeclareGlobalFunction("rec_iso_vec");
DeclareGlobalFunction("code_iso");
DeclareGlobalFunction("code_iso_vec");
DeclareGlobalFunction("ExtendCons");
DeclareGlobalFunction("OnSetOfLines");
DeclareGlobalFunction("OnSetOfSubspaces");
DeclareGlobalFunction("OnMultisetOfPoints");
DeclareGlobalFunction("testcons");
DeclareGlobalFunction("certsearch");
DeclareGlobalFunction("certsearch_vec");
DeclareGlobalFunction("certsearch_vec_prover");
DeclareGlobalFunction("certsearch_sss_prover");
DeclareGlobalFunction("pcode2rate");
DeclareGlobalFunction("clden_rvec");
DeclareGlobalFunction("certsearch_allrates");
DeclareGlobalFunction("testcons_vec");
DeclareGlobalFunction("testcons_withr");
DeclareGlobalFunction("OrbitsDomainSorted");
DeclareGlobalFunction("OrbitCan");
DeclareGlobalFunction("transportMapLazy");
DeclareGlobalFunction("transportMap");
DeclareGlobalFunction("transportMap_withusagestats");
DeclareGlobalFunction("bases1d");
DeclareGlobalFunction("baseskd");
DeclareGlobalFunction("baseskd_list");
DeclareGlobalFunction("baseskd_k");
DeclareGlobalFunction("OnSetOfSubspacesByCanonicalBasis");
DeclareGlobalFunction("LeiterspielWCons");
DeclareGlobalFunction("LeiterspielWCons_vec");
DeclareGlobalFunction("findcode");
DeclareGlobalFunction("LeiterspielWCons_vec_prover");
DeclareGlobalFunction("LeiterspielWCons_vec_prover_lazy");
DeclareGlobalFunction("DeepSort");
DeclareGlobalFunction("SortedPosition");
DeclareGlobalFunction("MyPosition");
DeclareGlobalFunction("transMapLazy");
DeclareGlobalFunction("LeiterspielWCons_rep_prover");
DeclareGlobalFunction("LeiterspielWCons_rep_prover_lazy");
DeclareGlobalFunction("LeiterspielWCons_rep_prover_withstats");
DeclareGlobalFunction("LeiterspielWCons_sss_prover_lazy");
DeclareGlobalFunction("extend_pcodes_sss_prover");
DeclareGlobalFunction("vecslist2rankvec");
DeclareGlobalFunction("rankvec2nsimple");
DeclareGlobalFunction("findrep");
DeclareGlobalFunction("proverep_withstats");
DeclareGlobalFunction("findrep_withstats");
DeclareGlobalFunction("extend_pcodes_vec");
DeclareGlobalFunction("IsSolvableNC2");
DeclareGlobalFunction("EdgeComp2");
DeclareGlobalFunction("sinkid");
DeclareGlobalFunction("IsReachable");
DeclareGlobalFunction("NC2coloredNC");
DeclareGlobalFunction("ColorEdges");
DeclareGlobalFunction("NC2colors");
DeclareGlobalFunction("ForestTransform2");
DeclareGlobalFunction("NCinstance2dag2");
DeclareGlobalFunction("IsClawmember");
DeclareGlobalFunction("NC2dagstruct");
DeclareGlobalFunction("Delnode");
DeclareGlobalFunction("Addnode2");
DeclareGlobalFunction("DeepCopy_rec");
DeclareGlobalFunction("DeepCopy_lol");
DeclareGlobalFunction("TopSort");
DeclareGlobalFunction("idmap");

DeclareGlobalFunction("skipline");
DeclareGlobalFunction("nextnum");
DeclareGlobalFunction("Readextfile");
DeclareGlobalFunction("writeinefile");
DeclareGlobalFunction("Readinefile");
DeclareGlobalFunction("rrcompute_lrs");
DeclareGlobalFunction("rrcompute");
DeclareGlobalFunction("conichull_lrs");
DeclareGlobalFunction("LeiterspielWCons_vec_lazy");
DeclareGlobalFunction("veccodegen");
DeclareGlobalFunction("rays2extfile");
DeclareGlobalFunction("trivialrates");
