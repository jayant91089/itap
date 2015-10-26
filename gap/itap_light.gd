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
#! All three questions above are very similar, in that, we are looking for a
#! linear representation of an integer polymatroid satisfying certain properties
#! (satisfying network coding constraints, access structure and having a specified rank vecor resp.)
#! In the most general form an achievability prover should be able to tell
#! if there exists a joint distribution satisfying certain constraints on
#! entropy function which remains a fundamental open problem. ITAP tries
#! answering this in a more restricted sense, i.e. with vector linear codes.
#! The algorithm underlying $\texttt{itap}$ is called Leiterspiel or the algorithm
#! of snakes and ladders. See <Cite Key="betten2006error"/> for details.
#! @Chapter Installation
#! To get the newest version of this GAP 4 package download one of the
#! archive files  itap-x.x.tar.gz, itap-x.x.zoo,  itap-x.x.tar.bz2, itap-x.x.zip
#! and unpack it using
#! $$\texttt{gunzip itap-x.x.tar.gz}$$
#! or
#! $$\texttt{unzoo -x itap-x.x.zoo}$$
#! respectively and so on.

#! Do this preferably (but not necessarily) inside the $\texttt{pkg}$ subdirectory
#! of your GAP 4 installation. It creates a subdirectory called $\texttt{itap}$.

#! This completes the installation of the package.

#! One can then start using $\texttt{itap}$ by invoking
#! @BeginCode Read
 LoadPackage( "itap");
 #! @EndCode
#! $$\texttt{gap>}$$
#! @InsertCode Read
#! from within GAP.
#! @BeginCode GF
q:=4;;
F:= GF(q);; # here q must be a prime power
#! @EndCode

#! @Chapter Usage
#! @Section Available functions
#!  In this section we shall look at the functions provided by $\texttt{itap}$.
#! @Description
#! This function checks if there is a linear representation of an integer polymatroid rank vector.
#! It accepts following arguments:
#! * $\texttt{rankvec}$ - A list of integers specifying a polymatroid rank vector
#! * $\texttt{nvars}$ - Number of ground set elements
#! * $\texttt{F}$ - The finite field over which we wish to find a linear representation. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $\texttt{optargs}$ is a list of optional arguments $\texttt{[lazy,..]}$ where
#!   * $\texttt{lazy}$ disables lazy evaluation of transporter maps if set to $\texttt{false}$, which is enabled by default
#!       in GAP.
#! Returns a list $\texttt{[true,code]}$ if there exists such a representation and $\texttt{code}$ is the vector linear code over $GF(q)$
#! Returns a list $\texttt{[false]}$ otherwise, indicating that no such representation exists
#! @Returns A list
#! @Arguments rankvec,nvars,F,optargs
DeclareGlobalFunction("proverep");
#! @Description
#!  This function checks if there is a vector linear code achieving the
#!  rate vector $\texttt{rvec}$ for the network coding instance $\texttt{ncinstance}$.
#! It accepts following arguments:
#! * $\texttt{ncinstance}$ is a list  $\texttt{[cons,nsrc,nvars]}$ containing 3 elements:
#!   * $\texttt{cons}$ is a list of network coding constraints.
#!   * $\texttt{nsrc}$ is the number of sources.
#!   * $\texttt{nvars}$ is the number of random variables associated with the network.
#! * $\texttt{rvec}$ - A list of $\texttt{nvars}$ integers specifying a rate vector
#! * $ \texttt{F}$ is the finite field over which we wish to find the vector linear code. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $\texttt{optargs}$ is a list of optional arguments $\texttt{[lazy,..]}$ where $\texttt{lazy}$ disables lazy evaluation
#!   of transporter maps if set to $\texttt{false}$, which is enabled by default.
#! Returns a list $\texttt{[true,code]}$ if there exists such a representation and $\texttt{code}$ is the vector linear code over $GF(q)$
#! Returns a list $\texttt{[false]}$ otherwise, indicating that no such code exists
#! @Returns A list
#! @Arguments ncinstance,rvec,F,optargs
DeclareGlobalFunction("proverate");
#! $\textbf{NOTE:}$ Certain naming convensions are followed while defining network coding instances. The source messages are labeled with
#! $\texttt{[1...nsrc]}$ while rest of the messages are labeled $\texttt{[nsrc...nvars]}$. Furthermore, the list $\texttt{cons}$ includes
#! all network constraints except source independence. This constraint is implied with the labeling i.e. $\texttt{itap}$
#! enforces it  by default for the messages labeled $\texttt{[1...nsrc]}$. See next section for usage examples.

#! @Description
#! This function checks if there is a multi-linear secret sharing scheme with secret and share
#! sizes given by $\texttt{svec}$ and the access structure $\texttt{Asets}$ with one dealer and
#! $\texttt{nvars-1}$ parties.
#! It accepts following arguments:
#! * $\texttt{Asets}$ - A list of authorized sets each specified as a subset of $[\texttt{nvars}-1]$
#! * $\texttt{nvars}$ - Number of participants (including one dealer)
#! * $\texttt{svec}$ - vector of integer share sizes understood as number of $\mathbb{F}_q$ symbols, with index 1 giving secret size and index $i,i\in \{2,...,\texttt{nvars}\}$ specifying share sizes of different parties
#! * $\texttt{F}$ - The finite field over which we wish to find a multi-linear scheme. It can be defined by invoking the following in GAP:
#!   @InsertCode GF
#! * $\texttt{optargs}$ is a list of optional arguments $\texttt{[lazy,..]}$ where
#!   * $\texttt{lazy}$ disables lazy evaluation of transporter maps if set to $\texttt{false}$, which is enabled by default
#!       in GAP.
#! Returns a list $\texttt{[true,code]}$ if there exists such a scheme and $\texttt{code}$ is the vector linear code over $GF(q)$
#! Returns a list $\texttt{[false]}$ otherwise, indicating that no such scheme exists
#! @Returns A list
#! @Arguments Asets,nvars,svec,F,optargs
DeclareGlobalFunction("provess");
#! $\textbf{NOTE:}$ No input checking is performed to verify if input $\texttt{Asets}$ follows labeling convensions. The map returned
#! with a linear scheme is a map $f:[\texttt{nvars}]\rightarrow [\texttt{nvars}]$ with dealer associated with label 1 and parties
#! associated with labels $\{2,...,\texttt{nvars}\}$. See next section for usage examples.

#! @Description
#!  Displays a network code (or an integer polymatroid).
#! It accepts 1 argument:
#! * $\texttt{code}$ - A list $\texttt{[s,map]}$ containing 2 elements:
#!   * $\texttt{s}$ - A list of subspaces where is subspace is itself a list of basis vectors
#!   * $\texttt{map}$ - A GAP record mapping subspaces in $\texttt{s}$ to network messages or to polymatroid ground set elements
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
DeclareGlobalFunction("BenaloahLeichter");

#! @Description
#!  Returns the access structure associated with Shamir's $(k,n)$ threshold scheme.
#!  See <Cite Key="Shamirhowto79"/> for details.
#! It accepts following arguments:
#! * $\texttt{n}$ - number of shares
#! * $\texttt{k}$ - threshold
#! @Returns A list of lists specifing authorized subsets of $[n]]$
#! @Arguments
DeclareGlobalFunction("Threshold");

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
DeclareGlobalFunction("veccodegen");
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
