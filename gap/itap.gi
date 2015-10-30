#############################################################################
##
##                                                      itap package
##
##  Copyright 2015,           Jayant Apte, Drexel University
##
##  The .gi file containing implementation part of the itap package.
##
#############################################################################

##
InstallGlobalFunction( set2int,
function(s)
  local i,j;
  i:=0;
  for j in s do
    i:=i+2^(Int(j)-1);
  od;
  return i;
end);

InstallGlobalFunction( Group2eqlist,
function(G,n)
  local i,eqlist,o,O1,x;
  O1:=OrbitsDomain(G,Combinations([1..n]),OnSets);
  eqlist:=[];
  for o in O1 do
    if Size(o)>1 then
      for i in [1..Size(o)-1] do
        x:=ZeroMutable([1..2^n]);
        x[set2int(o[i])+1]:=1;
        x[set2int(o[i+1])+1]:=-1;
        Append(eqlist,[x]);
      od;
    fi;
  od;
  return eqlist;
end);

InstallGlobalFunction(TranSub,
function(G,n)
  local t,c,Cn,Gs,O;
  t:=[];
  Cn:=ConjugacyClassesSubgroups(LatticeSubgroups(G));
  for c in Cn do
    Gs:=Representative(c);
    O:=OrbitsDomain(Gs,[1..n],OnPoints);
    if Size(O)=1 then
      Append(t,[Gs]);
    fi;
  od;
  return t;
end);

InstallGlobalFunction(partSub,
function(G,n)
  local t,c,Cn,Gs,O,osizes,o;
  t:=[];
  Cn:=ConjugacyClassesSubgroups(LatticeSubgroups(G));
  for c in Cn do
    Gs:=Representative(c);
    O:=OrbitsDomain(Gs,[1..n],OnPoints);
    osizes:=[];
    for o in O do
      Append(osizes,[Size(o)]);
    od;
    if AsSet(osizes)=[1,n-1] then
      Append(t,[Gs]);
    fi;
  od;
  return t;
end);

InstallGlobalFunction(FanoNet,
  function()
    local cons,nsrc,nvars;
    nvars:=7;
    nsrc:=3;
    cons:=[[[1,2],[1,2,4]],[[2,3],[2,3,5]],[[4,5],[4,5,6]],[[3,4],[3,4,7]],[[1,6],[3,1,6]],[[6,7],[2,6,7]],[[5,7],[1,5,7]]];
    return [cons,nsrc,nvars];
  end);



InstallGlobalFunction(NonFanoNet,
  function()
    local cons,nsrc,nvars;
    nvars:=7;
    nsrc:=3;
    cons:=[[[1,2,3],[1,2,3,4]],[[1,2],[1,2,5]],[[1,3],[1,3,6]],[[2,3],[2,3,7]],[[4,5],[3,4,5]],[[4,6],[2,4,6]],[[4,7],[1,4,7]]];
    return [cons,nsrc,nvars];
  end);

InstallGlobalFunction(VamosNet,
  function()
    local cons,nsrc,nvars;
    nvars:=8;
    nsrc:=4;
    cons:=[[[1,2,3,4],[1,2,3,4,5]],[[1,2,5],[1,2,5,6]],[[2,3,6],[2,3,6,7]],[[3,4,7],[3,4,7,8]],[[4,8],[2,4,8]],[[2,3,4,8],[1,2,3,4,8]],[[1,4,5,8],[1,2,3,4,5,8]],[[1,2,3,7],[1,2,3,4,7]],[[1,5,7],[1,3,5,7]]];
    return [cons,nsrc,nvars];
  end);

InstallGlobalFunction(U2kNet,
  function(k)
    local cons,nsrc,nvars,s2,s3;
    nvars:=k;
    nsrc:=2;
    cons:=[];
    for s2 in Combinations([1..k],2) do
          for s3 in Combinations([1..k],3) do
              if IsSubset(s3,s2) then
                  Append(cons,[[s2,s3]]);
              fi;
          od;
    od;
    return [cons,nsrc,nvars];
  end);

InstallGlobalFunction(ButterflyNet,
  function()
    return U2kNet(3);
  end);

InstallGlobalFunction(BenaloahLeichter,
  function()
  return [[1,2],[2,3],[3,4]];
  end);


InstallGlobalFunction(Threshold,
  function(n,k)
    return Combinations([1..n],k);
  end);

InstallGlobalFunction(MSdecomp,
  function(rvec,n)
    # decompose given polymatroid rank vector using Matus-Csirmaz decomposition
    local rvec_tight,rvec_mod,s,i,csum,delset;
    rvec_tight:= EmptyPlist(2^n-1);
    rvec_mod:= EmptyPlist(2^n-1);
    for s in Combinations([1..n]) do
      if Size(s)>0 then
        csum:=0;
        for i in s do
          delset:=[1..n];
          SubtractSet(delset,[i]);
          csum:=csum+rvec[set2int([1..n])]-rvec[set2int(delset)];
        od;
        rvec_tight[set2int(s)]:=rvec[set2int(s)]-csum;
        rvec_mod[set2int(s)]:=csum;
      fi;
    od;
    return [rvec_tight,rvec_mod];
  end);

InstallGlobalFunction( AppCns,
function(cons,n)
  # Returns a record mapping sets to constraint indices in cons
  local C,allvars,i,ncons,apc,s,aps,convars,con;
  allvars:=AsSet([]);
  ncons:=Size(cons);
  C:=Combinations([1..n]);
  apc:=rec();
  for s in C do
    i:=set2int(s);
    aps:=[];
    for con in cons do
      convars:=Union(AsSet(con[1]),AsSet(con[2]));
      if IsSubsetSet(s,convars) then
        Append(aps,[Position(cons,con)]);
      fi;
    od;
    apc.(i):=aps;
  od;
  return apc;
end);


InstallGlobalFunction(inv_pcode,
function(pcode)
  # Inverts a record
  local inv,k;
  inv:=rec();
  for k in RecNames(pcode) do
    inv.(pcode.(k)):=Int(k);
  od;
  return inv;
end);

InstallGlobalFunction(RecSetwise,
function(r,s)
  # access a record setwise
  local k,l;
  l:=[];
  for k in s do
    Append(l,[r.(k)]);
  od;
  return l;
end);

InstallGlobalFunction(SubRankMat,
function(veclist,pos)
  # rank of submatrix indexed by ``pos``
  return RankMat(veclist{pos});
end);

InstallGlobalFunction(SubRankMat_vec,
function(veclist,pos)
  # rank of submatrix indexed by ``pos``
  return RankMat(merge_veclist(veclist{pos}));
end);

InstallGlobalFunction(merge_veclist,
function(veclist)
  # return a single merge list of vectors
  local mlist,vlist,v;
  mlist:=[];
  for vlist in veclist do
    for v in vlist do
      Append(mlist,[v]);
    od;
  od;
  return mlist;
end);

InstallGlobalFunction(RecNamesInt,
function(r)
  # Returns all values in a record
  local i,intnames;
  intnames:=[];
  for i in RecNames(r) do
   Append(intnames,[Int(i)]);
  od;
  return intnames;
end);

InstallGlobalFunction(codedegrees,
function(veclist)
  local vecset,d,i,j,len1,len2;
  vecset:=AsSet(veclist);
  d:=rec();
  len1:=Size(vecset);
  len2:= Size(veclist);
  for i in [1..len1] do
    d.(i):=0;
    for j in [1..len2] do
      if veclist[j]=vecset[i] then
      d.(i):=d.(i)+1;
      fi;
    od;
  od;
  return d;
end);

InstallGlobalFunction(codedegrees_vec,
function(veclist,is_sane)
    # if is_sane=1, no sanity checks on veclist will be performed
    local vecset,d,i,j,len1,len2,len;
    len:=Size(veclist);
    if not is_sane = 1 then
      for i in [1..len] do
        veclist[i]:=AsSet(veclist[i]);
      od;
    fi;
    vecset:=AsSet(veclist);
    d:=rec();
    len1:=Size(vecset);
    len2:= Size(veclist);
    for i in [1..len1] do
      d.(i):=0;
      for j in [1..len2] do
        if AsSet(veclist[j])=AsSet(vecset[i]) then
        d.(i):=d.(i)+1;
        fi;
      od;
    od;
    return d;
end);

InstallGlobalFunction(extend_pcodes,
function(pcodelist,netcons,apc,nsrc,nvars)
  local ext_pcodelist,codelist,pcode,extlist,ext,rlist;
  ext_pcodelist:=[];
  codelist:=[];
  #Display(["extending",pcodelist]);
  for pcode in pcodelist do
    #Print(pcode[1]);
    Append(codelist,[pcode[1]]);
  od;
  extlist:=parallel_extensions(codelist);
  #Display(["All ext",extlist]);
  for ext in extlist do
    #Display(["Extension",ext,"parent pcode",pcodelist[ext[2]][2]]);
    rlist:=certsearch(ext[1],ShallowCopy(pcodelist[ext[2]][2]),netcons,apc,0,nsrc,nvars);
    if rlist[1]=true then
      Append(ext_pcodelist,[[ext[1],rlist[2]]]);
    fi;
  od;
  #Display(["Done with extending"]);
  return ext_pcodelist;
end);

InstallGlobalFunction(disp_scalar_pcode,
function(pcode,st)
  local imap,v;
    imap:=inv_pcode(pcode[2]);
    if not Size(st)=0 then
    #Display(st);
    fi;
    if(Size(pcode[1])>Size(RecNamesInt(imap))) then
      #Display("Deficient pcode");
    fi;
    for v in SortedList(RecNamesInt(imap)) do
      #Display([v,pcode[1][imap.(v)]]);
    od;
end);

InstallGlobalFunction(disp_subsparr,
function(v)
  local s;
  for s in v do
    Display(s);
    Display("=============================");
  od;
end);

InstallGlobalFunction(DisplayCode,
function(code)
  local i,s,map;
  s:=code[1];
  map:=code[2];
  for i in [1..Size(s)] do
    Display(Concatenation([String(i),"->",String(map.(i))]));
    Display(s[i]);
    Display("=============================");
  od;
end);

InstallGlobalFunction(Subspace5,
function()
local rays5;
  rays5:=[[       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       0,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1],[       0,       0,       0,       0,       0,       0,       0,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1],[       0,       0,       0,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1],[       0,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1],[       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1,       1],[       0,       0,       0,       1,       1,       1,       1,       1,       1,       1,       1,       2,       2,       2,       2,       1,       1,       1,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       0,       1,       1,       1,       1,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2],[       0,       1,       1,       1,       1,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       0,       2,       2,       1,       1,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       1,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       1,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       1,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2],[       1,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2],[       1,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       2,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2],[       2,       1,       2,       1,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       2,       2,       2,       1,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       1,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2,       2],[       0,       1,       1,       1,       1,       2,       2,       1,       1,       2,       2,       2,       2,       3,       3,       1,       1,       2,       2,       2,       2,       3,       3,       2,       2,       3,       3,       3,       3,       3,       3],[       0,       1,       1,       1,       1,       2,       2,       1,       1,       2,       2,       2,       2,       3,       3,       2,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       1,       1,       2,       2,       2,       1,       2,       2,       2,       2,       3,       3,       3,       1,       2,       2,       2,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       1,       1,       2,       2,       2,       1,       2,       2,       2,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       2,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       1,       2,       2,       3,       2,       3,       2,       3,       2,       2,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       2,       3,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       2,       3,       3,       3,       2,       3,       2,       3,       3,       3,       3,       3,       2,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       3,       1,       3,       1,       3,       2,       3,       1,       3,       2,       3,       2,       3,       3,       3,       1,       3,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3],[       3,       1,       3,       1,       3,       2,       3,       1,       3,       2,       3,       2,       3,       3,       3,       2,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3,       3],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       4,       1,       2,       2,       3,       2,       3,       3,       4,       2,       3,       3,       4,       3,       4,       4,       4],[       1,       1,       2,       1,       2,       2,       3,       1,       2,       2,       3,       2,       3,       3,       4,       3,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4],[       2,       1,       3,       1,       3,       2,       4,       1,       3,       2,       4,       2,       4,       3,       4,       1,       3,       2,       4,       2,       4,       3,       4,       2,       3,       3,       4,       3,       4,       4,       4],[       2,       1,       3,       1,       3,       2,       4,       1,       3,       2,       4,       2,       4,       3,       4,       1,       3,       2,       4,       2,       4,       3,       4,       2,       4,       3,       4,       3,       4,       4,       4],[       2,       2,       3,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       1,       3,       3,       4,       2,       4,       4,       4,       2,       3,       3,       4,       3,       4,       4,       4],[       2,       2,       3,       2,       3,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       3,       3,       4,       3,       4,       4,       4],[       2,       2,       4,       1,       2,       3,       4,       1,       3,       3,       4,       2,       3,       4,       4,       1,       3,       3,       4,       2,       3,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       1,       3,       3,       4,       2,       4,       3,       4,       2,       3,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       1,       3,       3,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       1,       3,       3,       4,       2,       4,       4,       4,       2,       4,       4,       4,       2,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       1,       3,       3,       4,       2,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       3,       4,       3,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       1,       3,       3,       4,       1,       3,       3,       4,       2,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       3,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       3,       4,       2,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       3,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       3,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       3,       3,       4,       2,       3,       3,       4,       4,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       2,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       3,       3,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       2,       3,       4,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       3,       4,       2,       3,       4,       4,       3,       4,       4,       4,       2,       3,       3,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       1,       2,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       3,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       3,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       1,       2,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       1,       3,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       2,       3,       3,       4,       3,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       2,       3,       4,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       3,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4,       2,       3,       3,       4,       4,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4,       2,       4,       4,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       2,       2,       4,       2,       4,       4,       4,       2,       4,       4,       4,       4,       4,       4,       4,       2,       4,       3,       4,       3,       4,       4,       4,       3,       4,       4,       4,       4,       4,       4,       4],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       4,       3,       4,       4,       5,       2,       3,       3,       4,       3,       4,       4,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       1,       2,       1,       2,       2,       3,       2,       3,       3,       4,       3,       4,       4,       5,       3,       4,       4,       5,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       1,       2,       2,       3,       3,       3,       2,       3,       3,       4,       4,       5,       5,       5,       3,       4,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       1,       2,       2,       3,       3,       4,       2,       3,       3,       4,       4,       5,       5,       5,       2,       3,       3,       4,       4,       5,       4,       5,       4,       5,       4,       5,       5,       5,       5,       5],[       1,       1,       2,       2,       3,       3,       4,       2,       3,       3,       4,       4,       5,       5,       5,       3,       4,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       3,       4,       2,       3,       3,       4,       4,       5,       4,       5,       2,       3,       4,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       3,       4,       2,       3,       4,       4,       4,       4,       5,       5,       3,       4,       4,       5,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       3,       4,       2,       3,       4,       5,       4,       5,       5,       5,       2,       3,       4,       4,       4,       4,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       3,       4,       2,       3,       4,       5,       4,       5,       5,       5,       2,       3,       4,       4,       4,       4,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       3,       4,       2,       3,       4,       5,       4,       5,       5,       5,       3,       4,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       4,       4,       4,       5,       5,       2,       3,       4,       4,       4,       4,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       4,       4,       4,       5,       5,       3,       3,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       4,       4,       4,       5,       5,       3,       4,       4,       5,       4,       5,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       4,       4,       4,       5,       5,       3,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       5,       4,       4,       5,       5,       2,       3,       4,       4,       4,       5,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       5,       4,       5,       4,       5,       2,       3,       4,       5,       4,       4,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       5,       4,       5,       4,       5,       3,       4,       5,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       5,       4,       5,       5,       5,       2,       3,       4,       5,       4,       4,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       2,       3,       4,       5,       4,       5,       5,       5,       3,       4,       5,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       3,       4,       5,       5,       4,       5,       5,       5,       3,       4,       4,       5,       5,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       3,       4,       5,       5,       5,       5,       5,       5,       3,       4,       4,       5,       4,       5,       5,       5,       4,       4,       5,       5,       5,       5,       5,       5],[       1,       2,       3,       2,       3,       4,       5,       3,       4,       5,       5,       5,       5,       5,       5,       3,       4,       5,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       3,       4,       4,       2,       3,       4,       4,       4,       4,       5,       5,       3,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       3,       4,       4,       2,       4,       4,       5,       4,       4,       5,       5,       3,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       3,       4,       4,       2,       4,       4,       5,       4,       5,       5,       5,       3,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       2,       4,       4,       5,       3,       5,       5,       5,       3,       5,       4,       5,       5,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       2,       4,       4,       5,       4,       5,       4,       5,       3,       4,       4,       5,       5,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       3,       5,       5,       5,       5,       5,       5,       5,       3,       4,       4,       5,       5,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       3,       5,       5,       5,       5,       5,       5,       5,       3,       4,       4,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       3,       5,       5,       5,       5,       5,       5,       5,       3,       5,       4,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       4,       2,       4,       4,       4,       3,       5,       4,       5,       4,       5,       5,       5,       3,       5,       4,       5,       4,       5,       5,       5,       4,       5,       5,       5,       5,       5,       5,       5],[       2,       2,       3,       2,       4,       4,       5,       2,       4,       4,       5,       4,       6,       6,       6,       2,       4,       4,       5,       4,       6,       5,       6,       4,       6,       5,       6,       6,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       5,       4,       5,       5,       6,       4,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       5,       5,       6,       2,       4,       4,       5,       4,       6,       5,       6,       4,       5,       6,       6,       6,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       5,       6,       2,       4,       4,       6,       4,       5,       5,       6,       4,       5,       5,       6,       6,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       5,       6,       2,       4,       4,       6,       4,       5,       6,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       5,       6,       2,       4,       4,       6,       4,       6,       5,       6,       4,       5,       6,       6,       5,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       6,       6,       2,       4,       4,       6,       4,       6,       5,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       6,       6,       2,       4,       4,       6,       4,       6,       5,       6,       4,       6,       5,       6,       5,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       6,       6,       2,       4,       4,       6,       4,       6,       6,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       2,       4,       4,       6,       4,       6,       6,       6,       4,       6,       5,       6,       5,       6,       6,       6,       5,       6,       6,       6,       6,       6,       6,       6],[       2,       2,       4,       2,       4,       4,       6,       4,       6,       6,       6,       6,       6,       6,       6,       4,       6,       5,       6,       5,       6,       6,       6,       5,       6,       6,       6,       6,       6,       6,       6],[       3,       2,       4,       2,       4,       4,       5,       2,       4,       4,       5,       4,       5,       6,       6,       2,       5,       4,       6,       4,       6,       6,       6,       4,       6,       6,       6,       6,       6,       6,       6],[       3,       2,       4,       2,       4,       4,       5,       2,       5,       4,       6,       4,       6,       6,       6,       2,       5,       4,       6,       4,       5,       5,       6,       4,       6,       6,       6,       6,       6,       6,       6],[       3,       2,       4,       2,       5,       4,       6,       2,       5,       4,       5,       4,       6,       6,       6,       2,       5,       4,       5,       4,       6,       6,       6,       4,       6,       6,       6,       6,       6,       6,       6],[       3,       2,       4,       2,       5,       4,       6,       2,       5,       4,       6,       4,       6,       6,       6,       2,       5,       4,       6,       4,       6,       5,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       3,       2,       5,       2,       5,       4,       6,       2,       5,       4,       6,       4,       5,       6,       6,       2,       5,       4,       5,       4,       6,       6,       6,       4,       6,       5,       6,       5,       6,       6,       6],[       3,       3,       5,       2,       4,       4,       6,       2,       4,       5,       6,       4,       5,       6,       6,       2,       5,       5,       6,       4,       6,       6,       6,       4,       5,       6,       6,       5,       6,       6,       6],[       3,       3,       5,       2,       4,       5,       6,       2,       4,       5,       6,       4,       5,       6,       6,       2,       5,       5,       6,       4,       6,       6,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       3,       3,       5,       3,       5,       5,       6,       2,       4,       4,       6,       5,       6,       6,       6,       2,       5,       5,       6,       5,       6,       6,       6,       4,       5,       5,       6,       5,       6,       6,       6],[       3,       3,       6,       2,       5,       5,       6,       1,       4,       4,       6,       3,       6,       6,       6,       4,       5,       5,       6,       6,       6,       6,       6,       5,       6,       6,       6,       6,       6,       6,       6],[       3,       3,       6,       2,       5,       5,       6,       2,       5,       5,       6,       3,       6,       6,       6,       1,       4,       4,       6,       3,       6,       5,       6,       3,       6,       5,       6,       4,       6,       6,       6],[       3,       3,       6,       2,       5,       5,       6,       2,       5,       5,       6,       4,       6,       6,       6,       1,       4,       4,       6,       3,       6,       5,       6,       3,       5,       6,       6,       4,       6,       6,       6],[       3,       3,       6,       2,       5,       5,       6,       2,       5,       5,       6,       4,       6,       6,       6,       1,       4,       4,       6,       3,       6,       6,       6,       3,       6,       5,       6,       4,       6,       6,       6],[       3,       3,       6,       3,       6,       5,       6,       2,       5,       4,       6,       4,       6,       6,       6,       2,       5,       4,       6,       5,       6,       6,       6,       4,       5,       5,       6,       6,       6,       6,       6],[       3,       3,       6,       3,       6,       6,       6,       2,       4,       4,       6,       4,       6,       6,       6,       2,       5,       5,       6,       5,       6,       6,       6,       4,       6,       5,       6,       5,       6,       6,       6],[       3,       3,       6,       3,       6,       6,       6,       2,       4,       4,       6,       5,       6,       6,       6,       2,       5,       5,       6,       5,       6,       6,       6,       4,       6,       6,       6,       5,       6,       6,       6],[       3,       3,       6,       3,       6,       6,       6,       3,       6,       5,       6,       5,       6,       6,       6,       3,       6,       5,       6,       5,       6,       6,       6,       4,       6,       6,       6,       6,       6,       6,       6],[       1,       2,       3,       3,       4,       5,       5,       3,       4,       5,       5,       6,       7,       7,       7,       4,       5,       6,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7],[       2,       2,       4,       2,       4,       4,       5,       2,       4,       4,       6,       4,       6,       6,       7,       3,       5,       5,       7,       5,       6,       6,       7,       5,       7,       7,       7,       7,       7,       7,       7],[       2,       2,       4,       2,       4,       4,       5,       3,       5,       5,       7,       5,       6,       6,       7,       3,       5,       5,       7,       5,       6,       6,       7,       5,       7,       7,       7,       7,       7,       7,       7],[       2,       2,       4,       2,       4,       4,       5,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       7,       5,       6,       6,       7,       6,       7,       6,       7,       7,       7,       7,       7],[       2,       2,       4,       2,       4,       4,       5,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       7,       5,       6,       6,       7,       6,       7,       7,       7,       6,       7,       7,       7],[       2,       2,       4,       2,       4,       4,       6,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       7,       5,       6,       6,       7,       6,       7,       7,       7,       6,       7,       7,       7],[       2,       2,       4,       3,       4,       4,       5,       3,       5,       5,       7,       6,       7,       7,       7,       4,       6,       6,       6,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7,       7],[       2,       2,       4,       3,       5,       5,       6,       3,       5,       5,       6,       5,       7,       7,       7,       3,       5,       5,       6,       5,       7,       6,       7,       5,       7,       6,       7,       7,       7,       7,       7],[       2,       2,       4,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       6,       7,       3,       5,       5,       7,       5,       7,       6,       7,       6,       7,       6,       7,       7,       7,       7,       7],[       2,       2,       4,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       6,       5,       6,       6,       7,       6,       7,       6,       7,       7,       7,       7,       7],[       2,       2,       4,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       7,       6,       7,       6,       7,       6,       7,       6,       7,       7,       7,       7,       7],[       2,       2,       4,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       7,       7,       4,       6,       6,       7,       7,       7,       7,       7,       5,       6,       6,       7,       7,       7,       7,       7],[       2,       3,       4,       3,       5,       5,       6,       3,       5,       5,       6,       6,       7,       7,       7,       3,       5,       6,       6,       6,       6,       7,       7,       6,       6,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       6,       3,       5,       5,       6,       6,       6,       7,       7,       4,       6,       5,       7,       6,       7,       7,       7,       6,       7,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       7,       3,       5,       5,       6,       6,       7,       7,       7,       3,       5,       5,       6,       6,       6,       7,       7,       6,       6,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       7,       3,       5,       5,       7,       5,       6,       7,       7,       3,       5,       6,       7,       5,       6,       7,       7,       6,       6,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       5,       6,       5,       6,       6,       7,       6,       7,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       7,       3,       5,       5,       7,       5,       7,       7,       7,       3,       5,       6,       7,       6,       6,       7,       7,       6,       6,       7,       7,       7,       7,       7,       7],[       2,       3,       5,       3,       5,       5,       7,       3,       5,       5,       7,       6,       7,       7,       7,       3,       5,       6,       6,       6,       6,       7,       7,       6,       6,       7,       7,       7,       7,       7,       7],[       3,       3,       6,       3,       6,       6,       6,       4,       7,       5,       7,       6,       7,       7,       7,       4,       7,       5,       7,       6,       7,       7,       7,       6,       7,       7,       7,       7,       7,       7,       7],[       4,       2,       6,       3,       6,       5,       8,       3,       6,       5,       7,       6,       8,       7,       8,       3,       6,       5,       7,       6,       8,       7,       8,       6,       8,       6,       8,       8,       8,       8,       8],[       4,       3,       6,       3,       6,       6,       8,       3,       6,       6,       8,       5,       8,       8,       8,       3,       7,       6,       8,       6,       8,       7,       8,       6,       7,       7,       8,       7,       8,       8,       8],[       4,       4,       6,       3,       6,       6,       8,       3,       6,       6,       8,       6,       8,       8,       8,       3,       6,       7,       8,       6,       7,       8,       8,       6,       7,       8,       8,       7,       8,       8,       8],[       4,       4,       8,       2,       6,       6,       8,       2,       6,       6,       8,       4,       8,       8,       8,       2,       6,       6,       8,       4,       8,       7,       8,       4,       8,       7,       8,       5,       8,       8,       8],[       3,       3,       6,       3,       6,       6,       7,       4,       6,       6,       8,       7,       8,       8,       9,       4,       7,       7,       9,       7,       8,       8,       9,       7,       9,       9,       9,       9,       9,       9,       9],[       3,       3,       6,       3,       6,       6,       9,       3,       6,       6,       9,       6,       9,       9,       9,       3,       6,       6,       9,       6,       8,       8,       9,       6,       8,       8,       9,       7,       9,       9,       9],[       3,       4,       7,       4,       7,       6,       9,       4,       7,       8,       8,       8,       8,       9,       9,       5,       7,       7,       9,       7,       9,       9,       9,       9,       9,       9,       9,       9,       9,       9,       9],[       4,       4,       7,       3,       7,       7,      10,       3,       7,       7,      10,       6,      10,      10,      10,       3,       7,       7,      10,       6,       8,       8,      10,       6,       9,       9,      10,       8,      10,      10,      10],[       3,       4,       7,       4,       7,       8,      11,       4,       7,       8,       9,       8,       9,      10,      11,       5,       8,       8,      11,       8,      11,      11,      11,       9,       9,      11,      11,      11,      11,      11,      11]];;
  return rays5;
end);

InstallGlobalFunction(extend_pcodes_vec,
 function(pcodelist,netcons,apc,nsrc,nvars,loopy)
    local ext_pcodelist,codelist,pcode,extlist,ext,rlist,xx;
    ext_pcodelist:=[];
    codelist:=[];
    #Display(["extending",pcodelist]);
    for pcode in pcodelist do
      #Print(pcode[1]);
      Append(codelist,[pcode[1]]);
    od;
    if loopy=false then
      extlist:=parallel_extensions_vec(codelist);
    else
      extlist:=nonsimple_extensions_vec(codelist);
    fi;
    #Display(["All ext",extlist]);
    if Size(pcodelist[1][1])=8 then
      #Display("parent list");
    #Display(codelist);
      #Display("extended codes");
      #Display(extlist);
    fi;
    xx:=0;
    for ext in extlist do
      #Display(["Extension",ext,"parent pcode",pcodelist[ext[2]][2]]);
      rlist:=certsearch_vec(ext[1],ShallowCopy(pcodelist[ext[2]][2]),netcons,apc,0,nsrc,nvars);
      xx:=xx+1;
      if rlist[1]=true then
        disp_scalar_pcode(pcodelist[ext[2]],"parent");
        #Display(["ext no.",xx]);
        disp_scalar_pcode([ext[1],rlist[2]],"child");
        Append(ext_pcodelist,[[ext[1],rlist[2]]]);
      fi;
    od;
    #Display(["Done with extending"]);
    return ext_pcodelist;
end);

InstallGlobalFunction(extend_pcodes_vec_prover,
function(pcodelist,netcons,apc,nsrc,nvars,loopy,rvec)
  local ext_pcodelist,codelist,pcode,extlist,ext,rlist,xx;
  ext_pcodelist:=[];
  codelist:=[];
  #Display(["extending",pcodelist]);
  for pcode in pcodelist do
    #Print(pcode[1]);
    Append(codelist,[pcode[1]]);
  od;
  if loopy=false then
    extlist:=parallel_extensions_vec(codelist);
  else
    extlist:=nonsimple_extensions_vec(codelist);
  fi;
  #Display(["All ext",extlist]);
  if Size(pcodelist[1][1])=8 then
    #Display("parent list");
    #Display(codelist);
    #Display("extended codes");
    #Display(extlist);
  fi;
  xx:=0;
  for ext in extlist do
    #Display(["Extension",ext,"parent pcode",pcodelist[ext[2]][2]]);
    rlist:=certsearch_vec_prover(ext[1],ShallowCopy(pcodelist[ext[2]][2]),netcons,apc,0,nsrc,nvars,rvec);
    xx:=xx+1;
    if rlist[1]=true then
      disp_scalar_pcode(pcodelist[ext[2]],"parent");
      #Display(["ext no.",xx]);
      disp_scalar_pcode([ext[1],rlist[2]],"child");
      Append(ext_pcodelist,[[ext[1],rlist[2]]]);
    fi;
  od;
  #Display(["Done with extending"]);
  return ext_pcodelist;
end);

InstallGlobalFunction(testcons_withrankvec,
function(veclist,pcode,rankvec,newvar)
  local newcons,c,ipcode,i,k,srcgnd,ssum,oldvars,newvar_rate,allsets,s,v;
  allsets:=IteratorOfCombinations(SortedList(RecSetwise(pcode,RecNamesInt(pcode))));
  ipcode:=inv_pcode(pcode);
  for s in allsets do
    if newvar in s then
      if not SubRankMat_vec(veclist,RecSetwise(ipcode,s))=rankvec[set2int(s)] then
        return false;
      fi;
    fi;
  od;
  return true;
end);

InstallGlobalFunction(IsAuthSet,
  function(s,Asets)
  local A;
  for A in Asets do
    if IsSubset(s,A) then
      return true;
    fi;
  od;
  return false;
end);

InstallGlobalFunction(certsearch_rep_prover_verbose,
function(veclist,pcode,rankvec,d,nvars)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  Print(["d=",d]);
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    rlist:=certsearch_rep_prover_verbose(veclist,ShallowCopy(pcode),rankvec,d+1,nvars);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if d=1 then
    Display("Defining 2nd variable");
  fi;
  if ret=true then
    return [true,pcode1];
  else
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      Display(["try mapping",d+1,v]);
      if testcons_withrankvec(veclist,ShallowCopy(pcode),rankvec,v) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return [true,pcode];
        else
          # go deeper in the tree
          Display(["Defined",d+1,v,"going deeper"]);
          rlist:=certsearch_rep_prover_verbose(veclist,ShallowCopy(pcode),rankvec,d+1,nvars);
          if rlist[1]=true then
            return [true,rlist[2]];
          else
            Display(["No feasible ext",d+1,v]);
          fi;
        fi;
      else
        # defn didn't work
        Display([d+1,v,"fail"]);
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);


InstallGlobalFunction(certsearch_rep_prover,
function(veclist,pcode,rankvec,d,nvars)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    rlist:=certsearch_rep_prover(veclist,ShallowCopy(pcode),rankvec,d+1,nvars);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if ret=true then
    return [true,pcode1];
  else
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #if Size(veclist) = 9 then
        #Display(["try mapping",d+1,v]);
      #fi;
      if testcons_withrankvec(veclist,ShallowCopy(pcode),rankvec,v) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          #Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return [true,pcode];
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          rlist:=certsearch_rep_prover(veclist,ShallowCopy(pcode),rankvec,d+1,nvars);
          if rlist[1]=true then
            return [true,rlist[2]];
          fi;
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);

InstallGlobalFunction(extend_pcodes_rep_prover,
function(rankvec, pcodelist,nvars,loopy)
  local ext_pcodelist,codelist,pcode,extlist,ext,rlist,xx;
  ext_pcodelist:=[];
  codelist:=[];
  #Display(["extending",pcodelist]);
  for pcode in pcodelist do
    #Print(pcode[1]);
    Append(codelist,[pcode[1]]);
  od;
  if loopy=false then
    extlist:=parallel_extensions_vec(codelist);
  else
    extlist:=nonsimple_extensions_vec(codelist);
  fi;
  #Display(["All ext",extlist]);
  xx:=0;
  for ext in extlist do
    #Display(["Extension",ext,"parent pcode",pcodelist[ext[2]][2]]);
    rlist:=certsearch_rep_prover(ext[1],ShallowCopy(pcodelist[ext[2]][2]),rankvec,0,nvars);
    xx:=xx+1;
    if rlist[1]=true then
      disp_scalar_pcode(pcodelist[ext[2]],"parent");
      #Display(["ext no.",xx]);
      disp_scalar_pcode([ext[1],rlist[2]],"child");
      Append(ext_pcodelist,[[ext[1],rlist[2]]]);
    fi;
  od;
  #Display(["Done with extending"]);
  return ext_pcodelist;
end);

InstallGlobalFunction(parallel_extensions,
function(veclistlist)
  local veclist,i,vecset,NonIsoList,veclist1,vec,IsNew,veclist2,tup;
  NonIsoList:=[];
  for i in [1..Size(veclistlist)] do
    veclist:=veclistlist[i];
    vecset:=AsSet(veclist);
    veclist1:=ShallowCopy(veclist);
    for vec in vecset do
      #Display(vec);
      Append(veclist1,[vec]);
      IsNew:=true;
      for tup in NonIsoList do
        veclist2:=tup[1];
        if code_iso(veclist1,veclist2) = true then
            #Display("bad");
            IsNew:=false;
            break;
        fi;
      od;
      if IsNew=true then
        #Display("Good");
        Append(NonIsoList,[[veclist1,i]]);
      fi;
      veclist1:=veclist1{[1..(Size(veclist1)-1)]};
    od;
  od;
  return NonIsoList;
end);

InstallGlobalFunction(parallel_extensions_vec,
function(veclistlist)
    # only parallel extensions. No loops added
    local vec,vecs,veclist,i,j,vecset,vecsset,len,NonIsoList,veclist1,IsNew,veclist2,tup;
    NonIsoList:=[];
    for i in [1..Size(veclistlist)] do
      veclist:=veclistlist[i];
      len:=Size(veclist);
      # clean code (sort)
      for j in [1..len] do
        veclist[j]:=AsSet(veclist[j]);
      od;
      vecsset:=AsSet(veclist);
      veclist1:=ShallowCopy(veclist);
      for vecs in vecsset do
        #Display(vec);
        Append(veclist1,[vecs]);
        IsNew:=true;
        for tup in NonIsoList do
          veclist2:=tup[1];
          if code_iso_vec(veclist1,veclist2) = true then
              #Display("bad");
              IsNew:=false;
              break;
          fi;
        od;
        if IsNew=true then
          #Display("Good");
          Append(NonIsoList,[[veclist1,i]]);
        fi;
        veclist1:=veclist1{[1..(Size(veclist1)-1)]};
      od;
    od;
    return NonIsoList;
end);

InstallGlobalFunction(zerovec,
function(k,ring)
  local v,i;
  v:=[];
    for i in [1..k] do
      Append(v,[0]);
    od;
  return ring*v;
end);

InstallGlobalFunction(nonsimple_extensions_vec,
function(veclistlist)
  #must have at least one vector in at least one set
  local vec,vecs,veclist,i,j,vecset,vecsset,len,NonIsoList,veclist1,IsNew,veclist2,tup,ring;
  NonIsoList:=[];
  for i in [1..Size(veclistlist)] do
    veclist:=veclistlist[i];
    len:=Size(veclist);
    # clean code (sort)
    for j in [1..len] do
      veclist[j]:=AsSet(veclist[j]);
    od;
    vecsset:=ShallowCopy(veclist);
    ring:=Z(Size(DefaultField(vecsset[1][1])));
    Append(vecsset,[[zerovec(Size(vecsset[1][1]),ring)]]);
    vecsset:=AsSet(vecsset);

    veclist1:=ShallowCopy(veclist);
    for vecs in vecsset do
      #Display(vec);
      Append(veclist1,[vecs]);
      IsNew:=true;
      for tup in NonIsoList do
        veclist2:=tup[1];
        if AsSet(veclist1)=AsSet(veclist2) then
          if code_iso_vec(veclist1,veclist2) = true then
            #Display("bad");
            IsNew:=false;
            break;
          fi;
        fi;
      od;
      if IsNew=true then
        #Display("Good");
        Append(NonIsoList,[[veclist1,i]]);
      fi;
      veclist1:=veclist1{[1..(Size(veclist1)-1)]};
    od;
  od;
  return NonIsoList;
end);

InstallGlobalFunction(rec2perm,
function(r,l,n)
  local leftrange,pl,k,j;
  leftrange:=[1..n];
  SubtractSet(leftrange,SortedList(RecSetwise(r,RecNamesInt(r))));
  pl:=EmptyPlist(n);
  k:=1;
  #Display([r,leftrange,n]);
  for j in [1..n] do
    #Display([j,k]);
    if j<=l then
      pl[j]:=r.(j);
    else
      pl[j]:=leftrange[k];
      k:=k+1;
    fi;
  od;
  #Display(PermList(pl));
  return PermList(pl);
end);

InstallGlobalFunction(rec_iso,
function(vecset,d1,d2,imap,d)
  local leftgnd,i,I,g,goodranks,S;
  if d=Size(vecset) then
    return true;
  fi;
  leftgnd:=[1..Size(vecset)];
  SubtractSet(leftgnd,SortedList(RecSetwise(imap,RecNamesInt(imap))));
  for i in [1..Size(leftgnd)] do
    # try d+1:=i map
    imap.(d+1):=leftgnd[i];
    #test size of parallel classes
    if d1.(d+1)=d2.(leftgnd[i]) then
      # test ranks
      I:=IteratorOfCombinations([1..d+1]);
      g:=rec2perm(imap,d+1,Size(vecset));
      goodranks:=true;
      for S in I do
        if d+1 in S then
          if not SubRankMat(vecset,S)=SubRankMat(vecset,OnSets(S,g)) then
            goodranks:=false;
            break;
          fi;
        fi;
      od;
      if goodranks=true then
        if rec_iso(vecset,d1,d2,imap,d+1)=true then
          return true;
        fi;
      fi;
    fi;
    Unbind(imap.(d+1));
  od;
  return false;
end);

InstallGlobalFunction(rec_iso_vec,
function(vecset,d1,d2,imap,d)
  local leftgnd,i,I,g,goodranks,S;
    if d=Size(vecset) then
      return true;
    fi;
    leftgnd:=[1..Size(vecset)];
    SubtractSet(leftgnd,SortedList(RecSetwise(imap,RecNamesInt(imap))));
    for i in [1..Size(leftgnd)] do
      # try d+1:=i map
      imap.(d+1):=leftgnd[i];
      #test size of parallel classes
      if d1.(d+1)=d2.(leftgnd[i]) then
        # test ranks
        I:=IteratorOfCombinations([1..d+1]);
        g:=rec2perm(imap,d+1,Size(vecset));
        goodranks:=true;
        for S in I do
          if d+1 in S then
            if not SubRankMat_vec(vecset,S)=SubRankMat_vec(vecset,OnSets(S,g)) then
              goodranks:=false;
              break;
            fi;
          fi;
        od;
        if goodranks=true then
          if rec_iso_vec(vecset,d1,d2,ShallowCopy(imap),d+1)=true then
            return true;
          fi;
        fi;
      fi;
      Unbind(imap.(d+1));
    od;
    return false;
end);

InstallGlobalFunction(code_iso,
function(veclist1,veclist2)
  local d1,d2,vecset;
  if not Size(veclist1) = Size(veclist2) then
    return false;
  fi;
  vecset:=AsSet(veclist1);
  d1:=codedegrees(veclist1);
  d2:=codedegrees(veclist2);
  return rec_iso(vecset,d1,d2,rec(),0);
end);

InstallGlobalFunction(code_iso_vec,
function(veclist1,veclist2)
  local d1,d2,vecset;
  if not Size(veclist1) = Size(veclist2) then
    return false;
  fi;
  vecset:=AsSet(veclist1);
  d1:=codedegrees_vec(veclist1,1);
  d2:=codedegrees_vec(veclist2,1);
  if not AsSet(RecSetwise(d1,RecNamesInt(d1))) = AsSet(RecSetwise(d2,RecNamesInt(d2))) then
    return false;
  fi;
  return rec_iso_vec(vecset,d1,d2,rec(),0);
end);


InstallGlobalFunction(ExtendCons,
function(netcons)
  local con,ext_netcons,sup,sub,comb,diff,c;
  ext_netcons:=ShallowCopy(netcons);
  for con in netcons do
    if IsSubsetSet(con[2],con[1]) then
      sub:=ShallowCopy(con[1]);
      sup:=ShallowCopy(con[2]);
    else
      sub:=ShallowCopy(con[2]);
      sup:=ShallowCopy(con[1]);
    fi;
    diff:=SortedList(ShallowCopy(sup));

    SubtractSet(diff,sub);
    comb:=Combinations(diff);
    SubtractSet(comb,[diff]);
    SubtractSet(comb,[[]]);
    for c in comb do
      Append(ext_netcons,[[sub,Union(c,sub)]]);
    od;
  od;
  return ext_netcons;
end);

InstallGlobalFunction(OnSetOfLines,
function ( sofl, g )
  local rl,lofl,len,i;
  len := Size( sofl );
  rl := [  ];
  lofl := AsList( sofl );
  for i  in [ 1 .. len ]  do
      Append( rl, [ OnLines( lofl[i], g ) ] );
  od;
  return AsSet( rl );
end);

InstallGlobalFunction(OnSetOfSubspaces,
function ( sofsofl, g )
  local rl,lofl,len,i,lofsofl;
  len := Size( sofsofl );
  rl := [  ];
  lofsofl := AsList( sofsofl );
  for i  in [ 1 .. len ]  do
      Append( rl, [ OnSetOfLines( lofsofl[i], g ) ] );
  od;
  return AsSet( rl );
end);

InstallGlobalFunction(OnMultisetOfPoints,
function ( msofp, g )
  # Assumes
  local rl,lofl,len,i;
  len := Size( msofp );
  rl := [  ];
  lofl := AsList( msofp );
  for i  in [ 1 .. len ]  do
      Append( rl, [ OnPoints( lofl[i], g ) ] );
  od;
  return AsSet( rl );
end);



InstallGlobalFunction(testcons,
function(veclist,pcode,nsrc,apc,newvar,netcons)
  local newcons,c,ipcode,i,k,srcgnd,ssum,oldvars;
  oldvars:=SortedList(RecSetwise(pcode,RecNamesInt(pcode)));
  newcons:= SortedList(apc.(set2int(oldvars)));
  SubtractSet(oldvars,AsList([newvar]));
  #Display(newcons);
  #Display(oldvars);
  SubtractSet(newcons,apc.(set2int(oldvars)));
  if Size(newcons)>0 or newvar<=nsrc then
    ipcode:=inv_pcode(pcode);
  fi;
  #Display(newcons);
  if Size(newcons)>0 then
    for i in newcons do
      c:=netcons[i];
      if not SubRankMat(veclist,RecSetwise(ipcode,c[1]))=SubRankMat(veclist,RecSetwise(ipcode,c[2])) then
        #Display(["edge con violated",c[1],c[2]]);
        return false;
      fi;
    od;
  fi;
  if newvar<=nsrc then
    srcgnd:=[];
    for k in RecNamesInt(pcode) do
      if pcode.(k)<=nsrc then
        Append(srcgnd,[k]);
      fi;
    od;
    ssum:=0;
    for i in srcgnd do
      ssum:=ssum+SubRankMat(veclist,[i]);
    od;
    if not ssum=SubRankMat(veclist,srcgnd) then
      #Display("source con violated");
      return false;
    fi;
  fi;
  return true;
end);

InstallGlobalFunction(certsearch,
function(veclist,pcode,netcons,apc,d,nsrc,nvars)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    #Display("first itrn, depth =");
    Print(d);
    Print(pcode);
    rlist:=certsearch(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if ret=true then
    return [true,pcode1];
  else
    #Display("Define var");
    #Print([d+1,pcode]);
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #Display("try mapping");
      #Print([d+1,v]);
      #Print(pcode);
      if testcons(SortedList(veclist),pcode,nsrc,apc,v,netcons) = true then
        #defn worked
        #Display(["Defined gnd:",d+1,"defvarssize",Size(defvars)]);
        if Size(defvars)+1=Size(veclist) then # we're finished
          return [true,pcode];
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          rlist:=certsearch(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
          if rlist[1]=true then
            return [true,rlist[2]];
          fi;
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);

InstallGlobalFunction(certsearch_vec,
function(veclist,pcode,netcons,apc,d,nsrc,nvars)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    #Display("first itrn, depth =");
    #Print(d);
    #Print(pcode);
    rlist:=certsearch_vec(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if ret=true then
    return [true,pcode1];
  else
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #if Size(veclist) = 9 then
        #Display(["try mapping",d+1,v]);
      #fi;
      if testcons_vec(veclist,ShallowCopy(pcode),nsrc,apc,v,netcons) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          #Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return [true,pcode];
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          rlist:=certsearch_vec(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
          if rlist[1]=true then
            return [true,rlist[2]];
          fi;
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);

InstallGlobalFunction(certsearch_vec_prover,
function(veclist,pcode,netcons,apc,d,nsrc,nvars,rvec)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    #Display("first itrn, depth =");
    #Print(d);
    #Print(pcode);
    rlist:=certsearch_vec_prover(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars,rvec);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if ret=true then
    return [true,pcode1];
  else
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #if Size(veclist) = 9 then
        #Display(["try mapping",d+1,v]);
      #fi;
      if testcons_withr(veclist,ShallowCopy(pcode),nsrc,apc,v,netcons,rvec) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          #Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return [true,pcode];
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          rlist:=certsearch_vec_prover(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars,rvec);
          if rlist[1]=true then
            return [true,rlist[2]];
          fi;
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);

InstallGlobalFunction(pcode2rate,
function(pcode)
  local rvec,ipmap,v;
  ipmap:=inv_pcode(pcode[2]);
  rvec:=[];
  for v in SortedList(RecNamesInt(ipmap)) do
    Append(rvec,[RankMat(pcode[1][ipmap.(v)])]);
  od;
  return rvec;
end);

InstallGlobalFunction(clden_rvec,
function(rvec)
  local denvec,r,d;
  denvec:=[];
  for r in rvec do
  Append(denvec,[DenominatorRat(r)]);
  od;
  d:=Lcm(denvec);
  return rvec*d;
end);



InstallGlobalFunction(certsearch_allrates,
function(veclist,pcode,netcons,apc,d,nsrc,nvars)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v,ratepts_child,temp_childrates;
  ret:=false;
  ratepts_child:=[];
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    #Display("first itrn, depth =");
    #Print(d);
    #Print(pcode);
    temp_childrates:=certsearch_allrates(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
    ratepts_child:=Union(ratepts_child,temp_childrates);
    #Append(ratepts_child,temp_childrates);
  fi;
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #if Size(veclist) = 9 then
        #Display(["try mapping",d+1,v]);
      #fi;
      if testcons_vec(veclist,ShallowCopy(pcode),nsrc,apc,v,netcons) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          #Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return AsSet([pcode2rate([veclist,pcode])]);
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          temp_childrates:=certsearch_allrates(veclist,ShallowCopy(pcode),netcons,apc,d+1,nsrc,nvars);
          ratepts_child:=Union(ratepts_child,temp_childrates);
          #Append(ratepts_child,temp_childrates);
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return ratepts_child;
end);





InstallGlobalFunction(testcons_vec,
function(veclist,pcode,nsrc,apc,newvar,netcons)
  local newcons,c,ipcode,i,k,srcgnd,ssum,oldvars;
  oldvars:=SortedList(RecSetwise(pcode,RecNamesInt(pcode)));
  newcons:= SortedList(apc.(set2int(oldvars)));
  SubtractSet(oldvars,AsList([newvar]));
  SubtractSet(newcons,apc.(set2int(oldvars)));
  if Size(newcons)>0 or newvar<=nsrc then
    ipcode:=inv_pcode(pcode);
  fi;
  #Display(newcons);
  if Size(newcons)>0 then
    for i in newcons do
      c:=netcons[i];
      #Display(veclist);
      if not SubRankMat_vec(veclist,RecSetwise(ipcode,c[1]))=SubRankMat_vec(veclist,RecSetwise(ipcode,c[2])) then
        #Display(["edge con violated",c[1],c[2]]);
        return false;
      fi;
    od;
  fi;
  if newvar<=nsrc then
    srcgnd:=[];
    for k in RecNamesInt(pcode) do
      if pcode.(k)<=nsrc then
        Append(srcgnd,[k]);
      fi;
    od;
    ssum:=0;
    for i in srcgnd do
      ssum:=ssum+SubRankMat_vec(veclist,[i]);
    od;
    if not ssum=SubRankMat_vec(veclist,srcgnd) then
      #Display("source con violated");
      return false;
    fi;
  fi;
  return true;
end);

#prover function
InstallGlobalFunction(testcons_withr,
function(veclist,pcode,nsrc,apc,newvar,netcons,rvec)
  local newcons,c,ipcode,i,k,srcgnd,ssum,oldvars,newvar_rate;
  oldvars:=SortedList(RecSetwise(pcode,RecNamesInt(pcode)));
  newcons:= SortedList(apc.(set2int(oldvars)));
  SubtractSet(oldvars,AsList([newvar]));
  #Display(newcons);
  #Display(oldvars);
  SubtractSet(newcons,apc.(set2int(oldvars)));
  #if Size(newcons)>0 or newvar<=nsrc then
  ipcode:=inv_pcode(pcode);
  #fi;
  newvar_rate:=RankMat(veclist[ipcode.(newvar)]);
  # test rate constraint
  if not newvar_rate=rvec[newvar] then
    return false;
  fi;
  #Display(newcons);
  if Size(newcons)>0 then
    for i in newcons do
      c:=netcons[i];
      #Display(veclist);
      if not SubRankMat_vec(veclist,RecSetwise(ipcode,c[1]))=SubRankMat_vec(veclist,RecSetwise(ipcode,c[2])) then
        #Display(["edge con violated",c[1],c[2]]);
        return false;
      fi;
    od;
  fi;
  if newvar<=nsrc then
    srcgnd:=[];
    for k in RecNamesInt(pcode) do
      if pcode.(k)<=nsrc then
        Append(srcgnd,[k]);
      fi;
    od;
    ssum:=0;
    for i in srcgnd do
      ssum:=ssum+SubRankMat_vec(veclist,[i]);
    od;
    if not ssum=SubRankMat_vec(veclist,srcgnd) then
      #Display("source con violated");
      return false;
    fi;
  fi;
  #Display(["testrates",newvar,newvar_rate,rvec[newvar],veclist[ipcode.(newvar)]]);
  return true;
end);

InstallGlobalFunction(OrbitsDomainSorted,
function(G,S,A)
 local i,orbs, out;
 orbs:=OrbitsDomain(G,S,A);
 out:=[];
 for i in [1..Size(orbs)] do
  out[i] := ShallowCopy(orbs[i]);
  Sort(out[i]);
 od;
 Sort(out);
 return out;
end);

InstallGlobalFunction(OrbitCan,
function(CanList,e)
  local c;
  for c in CanList do
    if Size(c[1])=Size(e) then
      return c[1];
    fi;
  od;
  return fail;
end);

InstallGlobalFunction(transportMapLazy,
function ( Aset, D, A, AonSets, phiR, psi, transMap,OrbitTrans,G)
 local z, t, Z, S, h, y, ly, lS, i, lzt,zt,lZ,rlist;
 if Size(Aset) = 1 then
  lZ:=SortedPosition(D,Aset[1],2);
  rlist:= transMapLazy(transMap,G,Aset[1],OrbitCan(OrbitTrans[1],Aset[1]),A,lZ);
  return rlist;
 fi;
 z:=Aset[Size(Aset)];
 Z:=Difference(Aset,[Aset[Size(Aset)]]);
 if Size(Z) = 1 then
  lZ:=SortedPosition(D,Z[1],2);
  rlist:= transMapLazy(transMap,G,Z[1],OrbitCan(OrbitTrans[1],Z[1]),A,lZ);
  t:=rlist[1];
  transMap:=rlist[2];
 else
  rlist:=transportMapLazy(Z,D,A,AonSets,phiR,psi,transMap,OrbitTrans,G);
  t:=rlist[1];
  transMap:=rlist[2];
 fi;
 S:=AonSets(Z,t);
 lS:=SortedPosition(OrbitTrans[Size(S)],S,4);
 zt:=A(z,t);
 lzt:=SortedPosition(D,zt,2);
 h:=phiR[Size(S)][lS][lzt];
 y:=A(zt,h);
 ly:=SortedPosition(D,y,2);
 if Size(psi[Size(S)][lS][ly]) = 0 then
  return [t*h,transMap];
 else
  return [t*h*psi[Size(S)][lS][ly][1],transMap];
 fi;
end);


InstallGlobalFunction(transportMap,
function ( Aset, D, A, AonSets, phiR, psi, transMap,OrbitTrans)
  local z, t, Z, S, h, y, ly, lS, i, lzt,zt,lZ;
  if Size(Aset) = 1 then
  lZ:=SortedPosition(D,Aset[1],2);
  return transMap[lZ];
  fi;
  z:=Aset[Size(Aset)];
  Z:=Difference(Aset,[Aset[Size(Aset)]]);
  if Size(Z) = 1 then
  lZ:=SortedPosition(D,Z[1],2);
  t:=transMap[lZ];
  else
  t:=transportMap(Z,D,A,AonSets,phiR,psi,transMap,OrbitTrans);
  fi;
  S:=AonSets(Z,t);
  lS:=SortedPosition(OrbitTrans[Size(S)],S,4);
  zt:=A(z,t);
  lzt:=SortedPosition(D,zt,2);
  h:=phiR[Size(S)][lS][lzt];
  y:=A(zt,h);
  ly:=SortedPosition(D,y,2);
  if Size(psi[Size(S)][lS][ly]) = 0 then
  return t*h;
  else
  return t*h*psi[Size(S)][lS][ly][1];
  fi;
end);

  # assumes that the argument is sorted
InstallGlobalFunction(transportMap_withusagestats,
function ( Aset, D, A, AonSets, phiR, psi, transMap,OrbitTrans,usedpts)
  local z, t, Z, S, h, y, ly, lS, i, lzt,zt,lZ,uu;
  if Size(Aset) = 1 then
  lZ:=SortedPosition(D,Aset[1],2);
  if not lZ in usedpts then
    usedpts:=Union(usedpts,[lZ]);
  fi;
  return [transMap[lZ],usedpts];
  fi;
  z:=Aset[Size(Aset)];
  Z:=Difference(Aset,[Aset[Size(Aset)]]);
  if Size(Z) = 1 then
  lZ:=SortedPosition(D,Z[1],2);
  if not lZ in usedpts then
    Union(usedpts,[lZ]);
  fi;
  t:=transMap[lZ];
  else
  uu:=transportMap_withusagestats(Z,D,A,AonSets,phiR,psi,transMap,OrbitTrans,usedpts);
  t:=uu[1];
  usedpts:=Union(usedpts,uu[2]);
  fi;
  S:=AonSets(Z,t);
  lS:=SortedPosition(OrbitTrans[Size(S)],S,4);
  zt:=A(z,t);
  lzt:=SortedPosition(D,zt,2);
  h:=phiR[Size(S)][lS][lzt];
  y:=A(zt,h);
  ly:=SortedPosition(D,y,2);
  if Size(psi[Size(S)][lS][ly]) = 0 then
  return [t*h,usedpts];
  else
  return [t*h*psi[Size(S)][lS][ly][1],usedpts];
  fi;
end);

InstallGlobalFunction(bases1d,
function ( q, d )
  local spclist,cblist,len,V,i;
  V := GF( q ) ^ d;
  spclist := AsList( Subspaces( V, 1 ) );
  cblist := [  ];
  len := Size( spclist );
  for i  in [ 1 .. len ]  do
      Append( cblist, AsList( CanonicalBasis( spclist[i] ) ) );
  od;
  return cblist;
end);

InstallGlobalFunction(baseskd,
function ( q, d ,k)
  # returns a list of lists, <=k-dim subspaces
  local spclist,cblist,len1,V,j,i;
  V := GF(q)^d;
  cblist := [  ];
  for j in [1..k] do # loop over dimension
    spclist := AsList( Subspaces( V, j ) );
    len1 := Size( spclist );
    for i  in [ 1 .. len1 ]  do # loop over subspaces
      Append( cblist, [AsList( CanonicalBasis( spclist[i] ) )] );
    od;
  od;
  return cblist;
end);

InstallGlobalFunction(baseskd_list,
function ( q, d ,klist)
  # returns a list of lists, specified subspaces
  local spclist,cblist,len1,V,j,i;
  V := GF(q)^d;
  cblist := [  ];
  for j in klist do # loop over dimension
    spclist := AsList( Subspaces( V, j ) );
    len1 := Size( spclist );
    for i  in [ 1 .. len1 ]  do # loop over subspaces
      Append( cblist, [AsList( CanonicalBasis( spclist[i] ) )] );
    od;
  od;
  return cblist;
end);

InstallGlobalFunction(baseskd_k,
function ( q, d ,k)
  # returns a list of lists, only the k-dim subspaces
  local spclist,cblist,len1,V,j,i;
  V := GF(q)^d;
  cblist := [  ];
  spclist := AsList( Subspaces( V, k ) );
  len1 := Size( spclist );
  for i  in [ 1 .. len1 ]  do # loop over subspaces
    Append( cblist, [AsList( CanonicalBasis( spclist[i] ) )] );
  od;
  return cblist;
end);



InstallGlobalFunction(OnSetOfSubspacesByCanonicalBasis,
function ( sofs, g )
  local len,rl,lofs,i;
      len := Size( sofs );
      rl := [  ];
      lofs := AsList( sofs );
      for i  in [ 1 .. len ]  do
          Append( rl, [ OnSubspacesByCanonicalBasis( lofs[i], g ) ] );
      od;
      return AsSet( rl );
end);

InstallGlobalFunction(LeiterspielWCons,
function(G,D,A,AonSets,max_simple,netcons,nsrc,nvars)
   local O, OrbitTrans, StabMap, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple;
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=[];
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      for j in [1..Size(O[i])] do
        k:=Position(D,O[i][j]);
        transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   for rep in OrbitTrans[1] do
    Append(PcodeList,[rec(1:=1)]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   apc:=AppCns(netcons,nvars);
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    #Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);

    #Display(["i",i,tempPcodeList]);
    for nrep in [1..Size(OrbitTrans[subsSize])] do
      #Display(OrbitTrans[subsSize][nrep]);
      #Display(PcodeList[nrep]);
    od;
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    search_success:=true;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        Sort(Rux);
        #Display(x);
        rlist:=certsearch(Rux,ShallowCopy(PcodeList[i]),netcons,apc,0,nsrc,nvars);
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            t:=transportMap(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans);
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=Position(OrbitTrans[subsSize],S);
            ltr:=Position(D,tr);
            h:=phiR[subsSize][lS][ltr];
            y:=A(tr,h);
            ly:=Position(D,y);
            if S=R and x=y then
              # we found a new group element of H
              H:=ClosureGroup(H,t*h);
              #gap uses a right group action
            else
              psi[subsSize][lS][ly]:=[Inverse(t*h)];
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;
   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
    od;
    AllCodes:=EmptyPlist(Size(OrbitTrans[max_simple]));
    for i in [max_simple+1..nvars] do
      #Display(["itrn",i]);
      surviving_simple:=0;
      for j in [1..Size(JointPcodeList)] do
        if Size(JointPcodeList[j])>0 then
          pcodelist:=JointPcodeList[j];
          pcodelist1:=extend_pcodes(pcodelist,netcons,apc,nsrc,nvars);
          if Size(pcodelist1)>0 then
            surviving_simple:=surviving_simple+1;
          fi;
          JointPcodeList[j]:=pcodelist1;
        fi;
      od;
      #Display(JointPcodeList);
      if surviving_simple=0 then
        search_success:=false;
        break;
      fi;
    od;
    if search_success=true then
      return [true,OrbitTrans,JointPcodeList];
    else
      return [false];
    fi;
   else
    return [false];
   fi;
end);

InstallGlobalFunction(LeiterspielWCons_vec,
function(G,D,A,AonSets,max_simple,netcons,nsrc,nvars,loopy)
   local O, OrbitTrans, StabMap, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple;
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=[];
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      for j in [1..Size(O[i])] do
        k:=Position(D,O[i][j]);
        transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   for rep in OrbitTrans[1] do
    Append(PcodeList,[rec(1:=1)]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   apc:=AppCns(netcons,nvars);
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    #Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);

    #Display(["i",i,tempPcodeList]);
    for nrep in [1..Size(OrbitTrans[subsSize])] do
      #Display(OrbitTrans[subsSize][nrep]);
      #Display(PcodeList[nrep]);
    od;
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Sort(Rux);
        #Display(x);
        rlist:=certsearch_vec(Rux,ShallowCopy(PcodeList[i]),netcons,apc,0,nsrc,nvars);
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            t:=transportMap(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans);
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
                # we found a new group element of H
                H:=ClosureGroup(H,t*h);
                #gap uses a right group action
              else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;
   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
    od;

    for i in [max_simple+1..nvars] do
      tempJointPcodeList:=[];
      #Display(["itrn",i,"npcodes",Size(JointPcodeList)]);
      surviving_simple:=0;
      for j in [1..Size(JointPcodeList)] do
        if Size(JointPcodeList[j])>0 then
          pcodelist:=JointPcodeList[j];
          pcodelist1:=extend_pcodes_vec(pcodelist,netcons,apc,nsrc,nvars,loopy);
          if Size(pcodelist1)>0 then
            surviving_simple:=surviving_simple+1;
            Append(tempJointPcodeList,[pcodelist1]);
          fi;
          #JointPcodeList[j]:=pcodelist1;
        fi;
      od;
      JointPcodeList:=ShallowCopy(tempJointPcodeList);
      #if i=3 then
      #  return JointPcodeList;
      #fi;
      #Display(JointPcodeList);
      if surviving_simple=0 then
        search_success:=false;
        break;
      fi;
    od;
    if search_success=true then
      return [true,OrbitTrans,JointPcodeList];
    else
      return [false];
    fi;
   else
    return [false];
   fi;
end);

InstallGlobalFunction(veccodegen,
function(ncinstance,F,d,k,s,optargs)
  local loopy,konly,A,AonSets,D,gl;
  # ncinstance: [cons,nsrc,nvars]
  #   cons: constraints as a list of list of lists
  #   nsrc: no. of sources
  #   nvars: no. of variables
  # F: a finite field over which codes are to be generated
  # d: maximum rank of underlying matroid
  # k: maximum singleton rank
  # s: maximum size of underlying simple matroid
  # optargs: [loopy,konly]
  # loopy: If true, then loopy codes will be generated
  # konly: If true, then only codes with singleton rank=k (or 0 based on 'loopy')
  #        will be generated
  gl:=GL(d,Size(F));
  A:= OnSubspacesByCanonicalBasis;
  AonSets:= OnSetOfSubspacesByCanonicalBasis;
  # Add cases here as per requirement
  if Size(optargs)>=2 then
    loopy:=optargs[1];
    konly:=optargs[2];
  elif Size(optargs)>=1 then
    loopy:=optargs[1];
    konly:=false;
  fi;
  if konly=true then
    D:=baseskd_k(Size(F),d,k);
  else
    D:=baseskd(Size(F),d,k);
  fi;
  return LeiterspielWCons_vec(gl,D,A,AonSets,s,ncinstance[1],ncinstance[2],ncinstance[3],loopy);
end);

InstallGlobalFunction(findcode,
function(ncinstance,F,d,k,s,rvec,optargs)
  local loopy,konly,A,AonSets,D,gl;
  # ncinstance: [cons,nsrc,nvars]
  #   cons: constraints as a list of list of lists
  #   nsrc: no. of sources
  #   nvars: no. of variables
  # F: a finite field over which codes are to be generated
  # d: maximum rank of underlying matroid
  # k: maximum singleton rank
  # s: maximum size of underlying simple matroid
  # rvec: rate vector to prove
  # optargs: [lazy,..]
  #   if lazy=false, disables lazy evaluation of transporter maps, default true
  if not IsPrimeField(F) then
    gl:=CollineationGroup(ProjectiveSpace(d-1,Size(F)));#GL(d,Size(F));
    A:= OnSubspaceByCollineation;#OnSubspacesByCanonicalBasis;
    AonSets:= OnSetOfSubspacesByCollineation;#OnSetOfSubspacesByCanonicalBasis;
    D:=ListOfSubspaces2VectorRep(baseskd(Size(F),d,k));
  else
   gl:=GL(d,Size(F));
   A:= OnSubspacesByCanonicalBasis;
   AonSets:= OnSetOfSubspacesByCanonicalBasis;
   D:=baseskd(Size(F),d,k);
  fi;
  if Size(optargs)=0 then
    return LeiterspielWCons_vec_prover_lazy(gl,D,A,AonSets,s,ncinstance[1],ncinstance[2],ncinstance[3],rvec,d);
  fi;
  if Size(optargs)=1 then
    if optargs[1]=false then
      return LeiterspielWCons_vec_prover(gl,D,A,AonSets,s,ncinstance[1],ncinstance[2],ncinstance[3],rvec,d);
    else
      return LeiterspielWCons_vec_prover_lazy(gl,D,A,AonSets,s,ncinstance[1],ncinstance[2],ncinstance[3],rvec,d);
    fi;
  fi;
end);



InstallGlobalFunction(LeiterspielWCons_vec_prover,
function(G,D,A,AonSets,max_simple,netcons,nsrc,nvars,rvec,coderank)
   local O, OrbitTrans, StabMap, init_rlist, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy;
   if 0 in rvec then
      loopy:=true;
   else
    loopy:=false;
   fi;
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=[];
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      for j in [1..Size(O[i])] do
        k:=Position(D,O[i][j]);
        transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element

   apc:=AppCns(netcons,nvars);
   for rep in OrbitTrans[1] do
    init_rlist:=certsearch_vec_prover(rep,rec(),netcons,apc,0,nsrc,nvars,rvec);
    Append(PcodeList,[init_rlist[2]]);
   od;
   for rep in OrbitTrans[1] do
    Append(PcodeList,[rec(1:=1)]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    #Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);

    #Display(["i",i,tempPcodeList]);
    for nrep in [1..Size(OrbitTrans[subsSize])] do
      #Display(OrbitTrans[subsSize][nrep]);
      #Display(PcodeList[nrep]);
    od;
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Sort(Rux);
        #Display(x);
        rlist:=certsearch_vec_prover(Rux,ShallowCopy(PcodeList[i]),netcons,apc,0,nsrc,nvars,rvec);
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            t:=transportMap(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans);
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
              # we found a new group element of H
              H:=ClosureGroup(H,t*h);
                #gap uses a right group action
              else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;

   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      # keep only the simple codes satisfying rank=d condition
      if coderank=SubRankMat_vec(OrbitTrans[max_simple][i],[1..max_simple]) then
        Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
      fi;
    od;
    if max_simple=nvars then
     return [true,JointPcodeList[1][1]];
    fi;
    for j in [1..Size(JointPcodeList)] do
      search_success:=true;
      pcodelist:=JointPcodeList[j];
      for i in [max_simple+1..nvars] do
        pcodelist1:=extend_pcodes_vec_prover(pcodelist,netcons,apc,nsrc,nvars,loopy,rvec);
        if Size(pcodelist1)=0 then
          search_success:=false;
          break;
        else
          pcodelist:=ShallowCopy(pcodelist1);
        fi;
      od;
      if search_success=true then
        return [true,pcodelist[1]];
      fi;
    od;
    return [false];
   else
    return [false];
   fi;
end);

InstallGlobalFunction(LeiterspielWCons_vec_prover_lazy,
function(G,D,A,AonSets,max_simple,netcons,nsrc,nvars,rvec,coderank)
   local O, OrbitTrans, StabMap,init_rlist, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,trlist;;
   if 0 in rvec then
      loopy:=true;
   else
    loopy:=false;
   fi;
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=EmptyPlist(Size(D));
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      #for j in [1..Size(O[i])] do
      #  k:=Position(D,O[i][j]);
      #  transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      #od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   apc:=AppCns(netcons,nvars);
   for rep in OrbitTrans[1] do
    init_rlist:=certsearch_vec_prover(rep,rec(),netcons,apc,0,nsrc,nvars,rvec);
    Append(PcodeList,[init_rlist[2]]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    #Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);

    #Display(["i",i,tempPcodeList]);
    for nrep in [1..Size(OrbitTrans[subsSize])] do
      #Display(OrbitTrans[subsSize][nrep]);
      #Display(PcodeList[nrep]);
    od;
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Sort(Rux);
        #Display(x);
        rlist:=certsearch_vec_prover(Rux,ShallowCopy(PcodeList[i]),netcons,apc,0,nsrc,nvars,rvec);
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            trlist:=transportMapLazy(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans,G);
            t:=trlist[1];
            transMap:=trlist[2];
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
              # we found a new group element of H
              H:=ClosureGroup(H,t*h);
                #gap uses a right group action
              else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;

   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      # keep only the simple codes satisfying rank=d condition
      if coderank=SubRankMat_vec(OrbitTrans[max_simple][i],[1..max_simple]) then
        Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
      fi;
    od;
    if max_simple=nvars then
     return [true,JointPcodeList[1][1]];
    fi;
    for j in [1..Size(JointPcodeList)] do
      search_success:=true;
      pcodelist:=JointPcodeList[j];
      for i in [max_simple+1..nvars] do
        pcodelist1:=extend_pcodes_vec_prover(pcodelist,netcons,apc,nsrc,nvars,loopy,rvec);
        if Size(pcodelist1)=0 then
          search_success:=false;
          break;
        else
          pcodelist:=ShallowCopy(pcodelist1);
        fi;
      od;
      if search_success=true then
        return [true,pcodelist[1]];
      fi;
    od;
    return [false];
   else
    return [false];
   fi;
end);

InstallGlobalFunction(DeepSort,
function(list,nlevels,l)
  local soretdlist,i;
  # l is current level
  # level:=1: only ``list`` is sorted at top level
  # level:=2: each element of list is also sorted and so on...
  # levels 1 and nlevels won't be sorted
  if nlevels = 1 then
    return list;
  fi;
  if nlevels=l then
    return list;
  else
    soretdlist:=EmptyPlist(Size(list));
    for i in [1..Size(list)] do
      soretdlist[i]:=DeepSort(list[i],nlevels,l+1);
      od;
    return soretdlist;
  fi;
end);


InstallGlobalFunction(SortedPosition,
function(list,e,nlevels)
  # Position function with DeepSort
  # elements of list and e must be iterables themself
  local i;
  for i in [1..Size(list)] do
    if SortedList(DeepSort(list[i],nlevels,1))=SortedList(DeepSort(e,nlevels-1,1)) then
      return i;
    fi;
  od;
  return fail;
end);

InstallGlobalFunction(MyPosition,
function(list,e)
  #Position function with DeepSort
  local i;
  for i in [1..Size(list)] do
    if list[i]=e then
      return i;
    fi;
  od;
  return fail;
end);

InstallGlobalFunction(transMapLazy,
function(transmap,G,e,c,A,pos)
  if not IsBound(transmap[pos]) then
    transmap[pos]:=RepresentativeAction(G,e,c,A);
  fi;
  return [transmap[pos],transmap];
end);

InstallGlobalFunction(LeiterspielWCons_rep_prover,
function(G,D,A,AonSets,max_simple,rankvec,nvars,coderank)
 local O, OrbitTrans, StabMap, init_rlist, transMap, k, j, i, subsSize,qq, transR, phiR, stabR, tempOrbs,
 l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,qqq,
 rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,trlist;
 if 0 in rankvec then
  loopy:=true;
 else
  loopy:=false;
 fi;
 O:=OrbitsDomainSorted(G,D,A);
 # List of Lists storing transversals
 OrbitTrans:=EmptyPlist(Size(D));
 OrbitTrans[1]:=[];
 StabMap:=EmptyPlist(Size(D));
 StabMap[1]:=[];
 transMap:=[];
 Display(["ntransporters",Size(D)]);
 # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
 PcodeList:=[];
 for i in [1..Size(O)] do
    OrbitTrans[1][i]:=[O[i][1]];
    StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
    for j in [1..Size(O[i])] do
        k:=Position(D,O[i][j]);
         transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
    od;
 od;
 # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
 for rep in OrbitTrans[1] do
  init_rlist:=certsearch_rep_prover(rep,rec(),rankvec,0,nvars);
  Append(PcodeList,[init_rlist[2]]);
 od;
 # compute applicable constraints for each subset of {1,...nvars}
 psi:=[];
 phiR:=[];
 tempPcodeList:=[];
 search_success:=true;
 # enumerate incrementally in subsSize
 for subsSize in [1..max_simple-1] do
  Display(["n=",subsSize]);
  #Display(["sets",Size(OrbitTrans[subsSize])]);
  #Display(["All set exts",OrbitTrans[subsSize]]);
  #Display(["pcodes",Size(tempPcodeList)]);
  tempPcodeList:=[];
  StabMap[subsSize+1]:=[];
  OrbitTrans[subsSize+1]:=[];
  if Size(OrbitTrans[subsSize])=0 then
   break;
  fi;
  transR:=[];
  phiR[subsSize]:=[];
  stabR:=[];
  for i in [1..Size(OrbitTrans[subsSize])] do
  # calculate the transversal and transporter
   transR[i]:=[];
   phiR[subsSize][i]:=[];
   stabR[i]:=[];
   tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
   for j in [1..Size(tempOrbs)] do
    transR[i][j] := tempOrbs[j][1];
    stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
    for k in [1..Size(tempOrbs[j])] do
     l:=Position(D,tempOrbs[j][k]);
     phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
    od;
   od;
  od;
  psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
  for i in [1..Size(OrbitTrans[subsSize])] do
   psi[subsSize][i]:=EmptyPlist(Size(D));
   for j in [1..Size(D)] do
    psi[subsSize][i][j]:=[];
   od;
  od;
  curLoc:=1;
  #for each set R in the transversal

  for i in [1..Size(OrbitTrans[subsSize])] do
   R:=OrbitTrans[subsSize][i];
   #Display("Try Extending");
   #Display(R);
   # for each x to augment it with
   for j in [1..Size(transR[i])] do
    lj:=Position(D,transR[i][j]);
    #Display(["Test x="]);
    if Size(psi[subsSize][i][lj])=0 then
    # this was undefined, so go here
      x:=transR[i][j];
      Rux:=ShallowCopy(R);
      Append(Rux,[x]);
      #Sort(Rux);
      #Display(x);
      rlist:=certsearch_rep_prover(Rux,ShallowCopy(PcodeList[i]),rankvec,0,nvars);
      #if rlist[1]=false then
      #  if Size(Rux)=3 then
      #  disp_subsparr(Rux);
      #  Display("///////////////////////////////");
      #  fi;
      #fi;
      if rlist[1]=true then
        H:=stabR[i][j];
        #caculate initial orbit under H in R
        if Size(R)>1 then
          rl:=OrbitsDomainSorted(H,R,A);
        else
          rl:=[R];
        fi;
        for ri in [1..Size(rl)] do
          r:=rl[ri][1];
          Rmrux:=Concatenation(Difference(R,[r]),[x]);
          Sort(Rmrux);
          # find the transporter for Rmrux
          t:=transportMap(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans);
          S:=AonSets(Rmrux,t);
          # S is now canonical representative
          tr:=A(r,t);
          lS:=SortedPosition(OrbitTrans[subsSize],S,4);
          if not lS=fail then
            ltr:=SortedPosition(D,tr,2);
            h:=phiR[subsSize][lS][ltr];
            y:=A(tr,h);
            ly:=SortedPosition(D,y,2);
            if S=R and x=y then
            # we found a new group element of H
            H:=ClosureGroup(H,t*h);
              #gap uses a right group action
            else
              psi[subsSize][lS][ly]:=[Inverse(t*h)];
            fi;
          fi;
        od;
        #Display(["i'",i,tempPcodeList]);
        Append(tempPcodeList,[rlist[2]]);
        Append(OrbitTrans[subsSize+1],[Rux]);
        StabMap[subsSize+1][curLoc]:=H;
        curLoc:=curLoc+1;
        #Display(["i''",i,tempPcodeList]);
      fi;
    fi;
   od;
  od;

 if Size(OrbitTrans[subsSize+1])=0 then
  search_success:=false;
  break;
 fi;
 PcodeList:=ShallowCopy(tempPcodeList);
 od;
 if search_success=true then
  JointPcodeList:=[];
  for i in [1..Size(OrbitTrans[max_simple])] do
    # keep only the simple codes satisfying rank=d condition
    if coderank=SubRankMat_vec(OrbitTrans[max_simple][i],[1..max_simple]) then
      Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
    fi;
  od;
  if max_simple=nvars then
     return [true,JointPcodeList[1][1]];
  fi;
  #Display(JointPcodeList);
  for j in [1..Size(JointPcodeList)] do
    search_success:=true;
    pcodelist:=JointPcodeList[j];
    for i in [max_simple+1..nvars] do
      pcodelist1:=extend_pcodes_rep_prover(rankvec,pcodelist,nvars,loopy);
      if Size(pcodelist1)=0 then
        search_success:=false;
        break;
      else
        pcodelist:=ShallowCopy(pcodelist1);
      fi;
    od;

    if search_success=true then
      return [true,pcodelist[1]];
    fi;
  od;
  return [false];
 else
  return [false];
 fi;
end);

InstallGlobalFunction(LeiterspielWCons_rep_prover_lazy,
function(G,D,A,AonSets,max_simple,rankvec,nvars,coderank)
   local O, OrbitTrans, StabMap,init_rlist, transMap, k, j, i, subsSize,qq, transR, phiR, stabR, tempOrbs,badS,badR,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,qqq,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,trlist;
   if 0 in rankvec then
    loopy:=true;
   else
    loopy:=false;
   fi;
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=EmptyPlist(Size(D));
   #Display(["ntransporters",Size(transMap)]);
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      #for j in [1..Size(O[i])] do
          # k:=Position(D,O[i][j]);
          # transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      #od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   for rep in OrbitTrans[1] do
    init_rlist:=certsearch_rep_prover(rep,rec(),rankvec,0,nvars);
    Append(PcodeList,[init_rlist[2]]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    #Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Sort(Rux);
        #Display(x);
        #badR:=[ [ [ 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2) ],      [ 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2) ],      [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ],   [ [ Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ], [ [ 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2) ] ] ];
        #badR:=[ [ [ 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2) ],      [ 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2) ],      [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ],   [ [ Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ]  ];
        #badR:=[ [ [ Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2) ],       [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ]  ];
        #badS:=[ [ [ 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2) ], [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ],  [ [ 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2) ],[ 0*Z(2), 0*Z(2), Z(2)^0, 0*Z(2), 0*Z(2) ], [ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ],  [ [ Z(2)^0, 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2) ],[ 0*Z(2), 0*Z(2), 0*Z(2), 0*Z(2), Z(2)^0 ] ] ];
        #if Rux=badS then
        #Display(["badS certsearch: pcode ",ShallowCopy(PcodeList[i])]);
        #fi;
        #if Rux=badR then
        #Display(["badR certsearch: pcode ",ShallowCopy(PcodeList[i])]);
        #fi;
        rlist:=certsearch_rep_prover(Rux,ShallowCopy(PcodeList[i]),rankvec,0,nvars);
        #if Rux=badS and rlist[1]=false then
        #Display("badS failed certsearch");
        #fi;
        #if Rux=badR and rlist[1]=true then
        #Display("badR passed certsearch");
        #fi;
        #if rlist[1]=false then
        #  if Size(Rux)=3 then
        #  disp_subsparr(Rux);
        #  Display("///////////////////////////////");
        #  fi;
        #fi;
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            trlist:=transportMapLazy(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans,G);
            t:=trlist[1];
            transMap:=trlist[2];
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            #if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
              # we found a new group element of H
              H:=ClosureGroup(H,t*h);
                #gap uses a right group action
              else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            #fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;

   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      # keep only the simple codes satisfying rank=d condition
      if coderank=SubRankMat_vec(OrbitTrans[max_simple][i],[1..max_simple]) then
        Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
      fi;
    od;
    if max_simple=nvars then
    qqq:=0;
    for qq in [1..Size(transMap)] do
      if IsBound(transMap[qq]) then
        qqq:=qqq+1;
      fi;
    od;
     return [true,JointPcodeList[1][1]];
    fi;
    #Display(JointPcodeList);
    for j in [1..Size(JointPcodeList)] do
      search_success:=true;
      pcodelist:=JointPcodeList[j];
      for i in [max_simple+1..nvars] do
        pcodelist1:=extend_pcodes_rep_prover(rankvec,pcodelist,nvars,loopy);
        if Size(pcodelist1)=0 then
          search_success:=false;
          break;
        else
          pcodelist:=ShallowCopy(pcodelist1);
        fi;
      od;

      if search_success=true then
        qqq:=0;
        for qq in [1..Size(transMap)] do
          if IsBound(transMap[qq]) then
            qqq:=qqq+1;
          fi;
        od;
        Display(["stats",qqq,Size(transMap)]);
        return [true,pcodelist[1]];
      fi;
    od;
    return [false];
   else
    return [false];
   fi;
end);

InstallGlobalFunction(LeiterspielWCons_rep_prover_withstats,
function(G,D,A,AonSets,max_simple,rankvec,nvars,coderank)
   local O, OrbitTrans, StabMap, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,tt,usedpts;
   if 0 in rankvec then
    loopy:=true;
   else
    loopy:=false;
   fi;
   usedpts:=[];
   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=[];
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      for j in [1..Size(O[i])] do
        k:=Position(D,O[i][j]);
        transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   for rep in OrbitTrans[1] do
    Append(PcodeList,[rec(1:=1)]);
   od;
   # compute applicable constraints for each subset of {1,...nvars}
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    Display(["n=",subsSize]);
    #Display(["sets",Size(OrbitTrans[subsSize])]);
    #Display(["All set exts",OrbitTrans[subsSize]]);
    #Display(["pcodes",Size(tempPcodeList)]);

    #Display(["i",i,tempPcodeList]);
    for nrep in [1..Size(OrbitTrans[subsSize])] do
      #Display(OrbitTrans[subsSize][nrep]);
      #Display(PcodeList[nrep]);
    od;
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     #Display("Try Extending");
     #Display(R);
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
      # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Sort(Rux);
        #Display(x);
        rlist:=certsearch_rep_prover(Rux,ShallowCopy(PcodeList[i]),rankvec,0,nvars);
        if rlist[1]=true then
          H:=stabR[i][j];
          #caculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            tt:=transportMap_withusagestats(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans,usedpts);
            t:=tt[1];
            usedpts:=Union(usedpts,tt[2]);
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
                # we found a new group element of H
                H:=ClosureGroup(H,t*h);
                #gap uses a right group action
                else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;

   if Size(OrbitTrans[subsSize+1])=0 then
    search_success:=false;
    break;
   fi;
   PcodeList:=ShallowCopy(tempPcodeList);
   od;

   Display(["transmaps used:",Size(usedpts),"/",Size(D)]);
   return;
   if search_success=true then
    JointPcodeList:=[];
    for i in [1..Size(OrbitTrans[max_simple])] do
      # keep only the simple codes satisfying rank=d condition
      if coderank=SubRankMat_vec(OrbitTrans[max_simple][i],[1..max_simple]) then
        Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]);
      fi;
    od;
    if max_simple=nvars then
     return [true,JointPcodeList[1][1]];
    fi;
    #Display(JointPcodeList);
    for j in [1..Size(JointPcodeList)] do
      search_success:=true;
      pcodelist:=JointPcodeList[j];
      for i in [max_simple+1..nvars] do
        pcodelist1:=extend_pcodes_rep_prover(rankvec,pcodelist,nvars,loopy);
        if Size(pcodelist1)=0 then
          search_success:=false;
          break;
        else
          pcodelist:=ShallowCopy(pcodelist1);
        fi;
      od;
      if search_success=true then
        return [true,pcodelist[1]];
      fi;
    od;
    return [false];
   else
    return [false];
   fi;
end);

InstallGlobalFunction(vecslist2rankvec,
function(vecslist)
  local rankvec,allsets,s;
  rankvec:=EmptyPlist(2^Size(vecslist)-1);
  allsets:=IteratorOfCombinations([1..Size(vecslist)]);
  for s in allsets do
    if not Size(s)=0 then
      rankvec[set2int(s)]:= SubRankMat_vec(vecslist,s);
    fi;
  od;
  return rankvec;
end);


InstallGlobalFunction(rankvec2nsimple,
function(rankvec,nvars)
  local leftvars,pc,pcs,pvars,i,j;
  # check if any singleton has a parallel class
  leftvars:=[1..nvars];#variables not in any parallel class sosfar
  pvars:=[]; #variables in some parallel class/loopy variables
  pcs:=[];
  for i in [1..nvars] do
    pc:=[];
    if not i in pvars then
      if rankvec[set2int([i])]=0 then
        Append(pvars,[i]);
      else
        for j in leftvars do
          if not i=j then
            if rankvec[set2int([i])]=rankvec[set2int([i,j])] then
              if rankvec[set2int([j])]=rankvec[set2int([i,j])] then
                Append(pc,[j]);
              fi;
            fi;
          fi;
        od;
        Append(pcs,[pc]);
        Append(pvars,pc);
        SubtractSet(leftvars,pc);
      fi;
    fi;
  od;
  return nvars-Size(pvars);
end);

InstallGlobalFunction(proverep,
function(rankvec,nvars,F,optargs)
  # optargs: [lazy,..]
  #    lazy: disables lazy evaluation of transporter maps if false, default true
  local d,nsimple,k,i,rlist,klist,lazy;
  # determine d
  d:=rankvec[set2int([1..nvars])];
  #Display(["d",d]);
  nsimple:=rankvec2nsimple(rankvec,nvars);
  #Display(["nsimple",nsimple]);
  # determine required k values
  klist:=[];
  for i in [1..nvars] do
    if not rankvec[set2int([i])] in klist then
      if rankvec[set2int([i])]>0 then
        Append(klist,[rankvec[set2int([i])]]);
      fi;
    fi;
  od;
  #Display(["klist",klist]);
  # find rep
  lazy:=true;
  if IsBound(optargs[1]) then
    lazy:=optargs[1];
  fi;
  rlist:=findrep2(rankvec,nvars,F,d,klist,nsimple,[lazy]);
  if rlist[1]=true then
    return rlist;
  else
    return [false];
  fi;
end);



InstallGlobalFunction(ListOfSubspaces2VectorRep,
function(los)
local rl,s,sl,v,vl,i;
  rl:=[];
  for s in los do
    sl:=[];
    for v in s do
    vl:=[];
      for i in [1..Size(v)] do
        Append(vl,[v[i]]);
      od;
      Append(sl,[ShallowCopy(vl)]);
    od;
    Append(rl,[ShallowCopy(sl)]);
  od;
  return rl;
end);

InstallGlobalFunction(OnSubspaceByCollineation,
function(s,g)
  #action on subspaces
  local ps,rs;
  if Size(s[1])=1 then
   return s;
  fi;
  ps:=ProjectiveSpace(Size(s[1])-1,Size(BaseField(g)));
  if Size(s)>1 then
    rs:=SortedList(Unpack(UnderlyingObject(OnProjSubspaces(VectorSpaceToElement(ps,s),g))));
    return AsList(CanonicalBasis(Subspace(BaseField(g)^Size(s[1]),rs)));
  else
    rs:=SortedList([Unpack(UnderlyingObject(OnProjSubspaces(VectorSpaceToElement(ps,s),g)))]);
    return AsList(CanonicalBasis(Subspace(BaseField(g)^Size(s[1]),rs)));
  fi;
end);

InstallGlobalFunction(OnSetOfSubspacesByCollineation,
function(sos,g)
# action on set of subspaces
  local rl,s;
  rl:=[];
  for s in sos do
  Append(rl,[OnSubspaceByCollineation(s,g)]);
  od;
  return rl;
end);


InstallGlobalFunction(findrep,
function(rankvec,nvars,F,d,klist,nsimple,optargs)
  local loopy,konly,A,AonSets,D,gl;
  # ncinstance: [cons,nsrc,nvars]
  #   cons: constraints as a list of list of lists
  #   nsrc: no. of sources
  #   nvars: no. of variables
  # F: a finite field over which codes are to be generated
  # d: maximum rank of underlying matroid
  # k: maximum singleton rank
  # s: maximum size of underlying simple matroid
  # rvec: rank vector whose representability we want to prove
  # optargs: [lazy,..]
  #   if lazy=false, disables lazy evaluation of transporter maps, default true
  #Display(["klist",klist]);
  #Display(["nsimple",nsimple]);
  gl:=GL(d,Size(F));
  A:= OnSubspacesByCanonicalBasis;
  AonSets:= OnSetOfSubspacesByCanonicalBasis;
  D:=baseskd_list(Size(F),d,klist);
  if Size(optargs)=0 then
    return LeiterspielWCons_rep_prover_lazy(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
  fi;
  if Size(optargs)=1 then
    if optargs[1]=false then
      #Display("Lazy eval disabled...");
      return LeiterspielWCons_rep_prover(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
    else
    #Display("Lazy eval enabled...");
      return LeiterspielWCons_rep_prover_lazy(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
    fi;
  fi;
  return LeiterspielWCons_rep_prover(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
end);

InstallGlobalFunction(findrep2,
function(rankvec,nvars,F,d,klist,nsimple,optargs)
  local loopy,konly,A,AonSets,D,gl;
  # ncinstance: [cons,nsrc,nvars]
  #   cons: constraints as a list of list of lists
  #   nsrc: no. of sources
  #   nvars: no. of variables
  # F: a finite field over which codes are to be generated
  # d: maximum rank of underlying matroid
  # k: maximum singleton rank
  # s: maximum size of underlying simple matroid
  # rvec: rank vector whose representability we want to prove
  # optargs: [lazy,..]
  #   if lazy=false, disables lazy evaluation of transporter maps, default true
  #Display(["klist",klist]);
  #Display(["nsimple",nsimple]);
  if not IsPrimeField(F) then
    gl:=CollineationGroup(ProjectiveSpace(d-1,Size(F)));#GL(d,Size(F));
    A:= OnSubspaceByCollineation;#OnSubspacesByCanonicalBasis;
    AonSets:= OnSetOfSubspacesByCollineation;#OnSetOfSubspacesByCanonicalBasis;
    D:=ListOfSubspaces2VectorRep(baseskd_list(Size(F),d,klist));
  else
    gl:=GL(d,Size(F));
    A:= OnSubspacesByCanonicalBasis;
    AonSets:= OnSetOfSubspacesByCanonicalBasis;
    D:=baseskd_list(Size(F),d,klist);
  fi;
  Display([gl,A,AonSets]);
  if Size(optargs)=0 then
    return LeiterspielWCons_rep_prover_lazy(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
  fi;
  if Size(optargs)=1 then
    if optargs[1]=false then
      #Display("Lazy eval disabled...");
      return LeiterspielWCons_rep_prover(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
    else
    #Display("Lazy eval enabled...");
      return LeiterspielWCons_rep_prover_lazy(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
    fi;
  fi;
  return LeiterspielWCons_rep_prover(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
end);


InstallGlobalFunction(proverep_withstats,
function(rankvec,nvars,F,optargs)
  # optargs: [force_nsimple,..]
  #    force_nsimple: forces the prover to use only the simple codes of specified length
  local d,nsimple,k,i,rlist,klist;
  # determine d
  d:=rankvec[set2int([1..nvars])];
  Display(["d",d]);
  nsimple:=rankvec2nsimple(rankvec,nvars);
  Display(["nsimple",nsimple]);
  # determine required k values
  klist:=[];
  for i in [2..nvars] do
    if not rankvec[set2int([i])] in klist then
      Append(klist,[rankvec[set2int([i])]]);
    fi;
  od;
  Display(["klist",klist]);
  # find rep
  findrep_withstats(rankvec,nvars,F,d,klist,nsimple);
end);

InstallGlobalFunction(findrep_withstats,
function(rankvec,nvars,F,d,klist,nsimple)
  local loopy,konly,A,AonSets,D,gl;
  # ncinstance: [cons,nsrc,nvars]
  #   cons: constraints as a list of list of lists
  #   nsrc: no. of sources
  #   nvars: no. of variables
  # F: a finite field over which codes are to be generated
  # d: maximum rank of underlying matroid
  # k: maximum singleton rank
  # s: maximum size of underlying simple matroid
  # rvec: rate vector to prove
  gl:=GL(d,Size(F));
  A:= OnSubspacesByCanonicalBasis;
  AonSets:= OnSetOfSubspacesByCanonicalBasis;
  D:=baseskd_list(Size(F),d,klist);
  LeiterspielWCons_rep_prover_withstats(gl,D,A,AonSets,nsimple,rankvec,nvars,d);
end);

InstallGlobalFunction(proverate,
function(ncinstance,rvec,F,optargs)
  # optargs: [force_nsimple,lazy,..]
  #    force_nsimple: boolean that forces the prover to use only the simple codes of specified length,default false
  #    lazy: a boolean indicating whether transporter maps will be evaluated lazily,default true
  local d,cons,nsrc,nvars,rlist,i,min_simple,max_simple,nsimple,lazy,k;
  k:=Maximum(rvec);
  cons:=ncinstance[1];
  nsrc:=ncinstance[2];
  nvars:=ncinstance[3];
  # determine d
  d:=0;
  for i in [1..nsrc] do
    d:=d+rvec[i];
  od;
  if d=0 then
    return [true,"trivial"];
  fi;
  lazy:=true;
  if Size(optargs)=0 then
    min_simple:=d;
    max_simple:=nvars;

  else
    if IsBound(optargs[1]) then
      min_simple:=optargs[1];
      max_simple:=optargs[1];
    else
      min_simple:=d;
      max_simple:=nvars;
    fi;

    if Size(optargs)>1 then
      lazy:=optargs[2];
    fi;
  fi;
  for nsimple in [min_simple..max_simple] do
    rlist:=findcode(ncinstance,F,d,k,nsimple,rvec,[lazy]);
    if rlist[1]=true then
      return rlist;
    fi;
  od;
  return [false,[]];
end);

InstallGlobalFunction(provess,
function(Asets,nvars,svec,F,optargs)
  # optargs: [lazy,..]
  #    lazy: disables lazy evaluation of transporter maps if false, default true
  local d,nsimple_list,k,i,rlist,klist,lazy;
  # d will be swept from s to p(n-1)+s-1
  Asets:=Asets+1;
  # determine required k values
  #spl
  klist:=AsList(AsSet(svec));
  #Display(["klist",klist]);
  if Size(klist)=1 then # protect agains all zero shares
    if klist[1]=0 then
      return [true,"trivial"];
    fi;
  fi;
  # find rep
  lazy:=true;
  if IsBound(optargs[1]) then
    lazy:=optargs[1];
  fi;
  for d in [Maximum(svec)..Sum(svec)-1] do
    #spl
    #d:=2;
    #Display(["d",d]);
    nsimple_list:= [2..nvars];
    rlist:=findsss(Asets,nvars,svec,F,d,klist,nsimple_list,[lazy]);
    #Display(rlist);
    if rlist[1]=true then
      return rlist;
    fi;
  od;
  return [false];
end);

InstallGlobalFunction(findsss,
  function(Asets,nvars,svec,F,d,klist,nsimple_list,optargs)
    local gl,A,AonSets,D,slist;
    #Display(gl);
    if not IsPrimeField(F) then
      gl:=CollineationGroup(ProjectiveSpace(d-1,Size(F)));#GL(d,Size(F));
      A:= OnSubspaceByCollineation;#OnSubspacesByCanonicalBasis;
      AonSets:= OnSetOfSubspacesByCollineation;#OnSetOfSubspacesByCanonicalBasis;
      D:=ListOfSubspaces2VectorRep(baseskd_list(Size(F),d,klist));
    else
      gl:=GL(d,Size(F));
      A:= OnSubspacesByCanonicalBasis;
      AonSets:= OnSetOfSubspacesByCanonicalBasis;
      D:=baseskd_list(Size(F),d,klist);
    fi;
    #Display(["nsimple list",nsimple_list]);
    if Size(optargs)=0 then
      return LeiterspielWCons_sss_prover_lazy(gl,D,A,AonSets,nsimple_list,Asets,nvars,svec,d);
    fi;
    if Size(optargs)=1 then
      if optargs[1]=false then
        return LeiterspielWCons_sss_prover_lazy(gl,D,A,AonSets,nsimple_list,Asets,nvars,svec,d);
      else
        return LeiterspielWCons_sss_prover_lazy(gl,D,A,AonSets,nsimple_list,Asets,nvars,svec,d);
      fi;
    fi;
  end);

InstallGlobalFunction(LeiterspielWCons_sss_prover_lazy,
function(G,D,A,AonSets,nsimple_list,Asets,nvars,svec,coderank)
   local O, OrbitTrans, StabMap,init_rlist, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,trlist;;

   # no loops (assumption). If there are loops in sss, access structure is degenerate
   loopy:=false;

   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=EmptyPlist(Size(D));
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   PcodeList:=[];
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
      #for j in [1..Size(O[i])] do
      #  k:=Position(D,O[i][j]);
      #  transMap[k]:=RepresentativeAction(G,O[i][j],O[i][1],A);
      #od;
   od;
   # initialize PcodeList with lexicographically smallest pcode rec(1:=1) for each transversal element
   #apc:=AppCns(netcons,nvars)
   #Display(OrbitTrans[1]);
   for rep in OrbitTrans[1] do
    init_rlist:=certsearch_sss_prover(rep,rec(),0,Asets,nvars,svec);
    Append(PcodeList,[init_rlist[2]]);
   od;
   #Display(["PcodeList",PcodeList]);
   # compute applicable constraints for each subset of {1,...nvars}
   psi:=[];
   phiR:=[];
   tempPcodeList:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..nvars-1] do
    #Display(["n",subsSize]);
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    #Display(["no. po poly",Size(OrbitTrans[subsSize])]);
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
      # calculate the transversal and transporter
      transR[i]:=[];
      phiR[subsSize][i]:=[];
      stabR[i]:=[];
      tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
      for j in [1..Size(tempOrbs)] do
        transR[i][j] := tempOrbs[j][1];
        stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
        for k in [1..Size(tempOrbs[j])] do
          l:=Position(D,tempOrbs[j][k]);
          phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
        od;
      od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal

    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];
     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      if Size(psi[subsSize][i][lj])=0 then
        # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);
        #Display(x);
        #Sort(Rux);
        #Display(["test",R,x]);
        rlist:=certsearch_sss_prover(Rux,ShallowCopy(PcodeList[i]),0,Asets,nvars,svec);
        if rlist[1]=true then
          H:=stabR[i][j];
          #calculate initial orbit under H in R
          if Size(R)>1 then
            rl:=OrbitsDomainSorted(H,R,A);
          else
            rl:=[R];
          fi;
          for ri in [1..Size(rl)] do
            r:=rl[ri][1];
            Rmrux:=Concatenation(Difference(R,[r]),[x]);
            Sort(Rmrux);
            # find the transporter for Rmrux
            trlist:=transportMapLazy(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans,G);
            t:=trlist[1];
            transMap:=trlist[2];
            S:=AonSets(Rmrux,t);
            # S is now canonical representative
            tr:=A(r,t);
            lS:=SortedPosition(OrbitTrans[subsSize],S,4);
            if not lS=fail then
              ltr:=SortedPosition(D,tr,2);
              h:=phiR[subsSize][lS][ltr];
              y:=A(tr,h);
              ly:=SortedPosition(D,y,2);
              if S=R and x=y then
                # we found a new group element of H
                H:=ClosureGroup(H,t*h);
                #gap uses a right group action
              else
                psi[subsSize][lS][ly]:=[Inverse(t*h)];
              fi;
            fi;
          od;
          #Display(["i'",i,tempPcodeList]);
          Append(tempPcodeList,[rlist[2]]);
          Append(OrbitTrans[subsSize+1],[Rux]);
          StabMap[subsSize+1][curLoc]:=H;
          curLoc:=curLoc+1;
          #Display(["i''",i,tempPcodeList]);
        fi;
      fi;
     od;
    od;

    if Size(OrbitTrans[subsSize+1])=0 then
      return [false];
    elif subsSize+1 in nsimple_list then
      # nonsimple extensions are performed
      JointPcodeList:=[];
      for i in [1..Size(OrbitTrans[subsSize+1])] do
        # keep only the simple codes satisfying rank=d condition
        if coderank=SubRankMat_vec(OrbitTrans[subsSize+1][i],[1..subsSize+1]) then
          Append(JointPcodeList,[[[ShallowCopy(OrbitTrans[subsSize+1][i]),tempPcodeList[i]]]]);
        fi;
      od;
      #Display(JointPcodeList);
      if subsSize+1=nvars then
        if Size(JointPcodeList)>0 then
          return [true,JointPcodeList[1][1]];
        else
          return [false];
        fi;
      fi;
      for j in [1..Size(JointPcodeList)] do
        pcodelist:=JointPcodeList[j];
        search_success:=true;
        for i in [subsSize+1+1..nvars] do
          pcodelist1:=extend_pcodes_sss_prover(pcodelist,Asets,nvars,svec,loopy);
          if Size(pcodelist1)=0 then
            search_success:=false;
            break;
          else
            pcodelist:=ShallowCopy(pcodelist1);
          fi;
        od;
        if search_success=true then
          return [true,pcodelist[1]];
        fi;
      od;
    fi;
    PcodeList:=ShallowCopy(tempPcodeList);
    od;
    return [false];
    # non-simple extension: isomorphism testing is polynomial time for
    # non-simple extensions of same simple polymatroid

end);

InstallGlobalFunction(extend_pcodes_sss_prover,
function(pcodelist,Asets,nvars,svec,loopy)
  local ext_pcodelist,codelist,pcode,extlist,ext,rlist,xx;
  ext_pcodelist:=[];
  codelist:=[];
  #Display(["extending",pcodelist]);
  for pcode in pcodelist do
    #Print(pcode[1]);
    Append(codelist,[pcode[1]]);
  od;
  if loopy=false then
    extlist:=parallel_extensions_vec(codelist);
  else
    extlist:=nonsimple_extensions_vec(codelist);
  fi;
  #Display(["All ext",extlist]);
  xx:=0;
  for ext in extlist do
    #Display(["Extension",ext,"parent pcode",pcodelist[ext[2]][2]]);
    rlist:=certsearch_sss_prover(ext[1],ShallowCopy(pcodelist[ext[2]][2]),0,Asets,nvars,svec);
    xx:=xx+1;
    if rlist[1]=true then
      disp_scalar_pcode(pcodelist[ext[2]],"parent");
      #Display(["ext no.",xx]);
      disp_scalar_pcode([ext[1],rlist[2]],"child");
      Append(ext_pcodelist,[[ext[1],rlist[2]]]);
    fi;
  od;
  #Display(["Done with extending"]);
  return ext_pcodelist;
end);

InstallGlobalFunction(testcons_ss,
function(veclist,pcode,Asets,svec,newvar)
  local allsets,ipcode,veclist_ext,s,defparties;
  ipcode:=inv_pcode(pcode);
  if not svec[newvar]=RankMat(veclist[ipcode.(newvar)]) then
    return false;
  fi;
  defparties:=SortedList(RecSetwise(pcode,RecNamesInt(pcode)));
  if 1 in defparties then
    SubtractSet(defparties,[1]);
    if Size(defparties)>0 then
      allsets:=IteratorOfCombinations(defparties);

      #veclist_ext:=[];
      #Append(veclist_ext,[sspace]);
      #Append(veclist_ext,veclist);
      for s in allsets do
        #Display(["s",s]);
        if Size(s)>0 then
          if newvar in s or newvar=1  then
            # test if s is in Asets
            #Display("valid");
            if s in Asets then
              #Display(["test1",RecSetwise(ipcode,s),Union(RecSetwise(ipcode,s)+1,[1])]);
              if not SubRankMat_vec(veclist,RecSetwise(ipcode,s))= SubRankMat_vec(veclist,Union(RecSetwise(ipcode,s),[1])) then
                #Display("test1fail");
                return false;
              fi;
            elif not IsAuthSet(s,Asets)  then
                #Display(["test2",RecSetwise(ipcode,s),Size(sspace),Union(RecSetwise(ipcode,s)+1,[1])]);
                if not SubRankMat_vec(veclist,RecSetwise(ipcode,s))+SubRankMat_vec(veclist,RecSetwise(ipcode,[1]))= SubRankMat_vec(veclist,Union(RecSetwise(ipcode,s),[1])) then
                  #Display("test2fail");
                  return false;
                fi;
            fi;
          fi;
        fi;
      od;
    fi;
  fi;
  return true;
  end);

InstallGlobalFunction(certsearch_sss_prover,
function(veclist,pcode,d,Asets,nvars,svec)
  local ret,rlist,pcode1,lex_pivot,k,lexvars,defvars,v;
  ret:=false;
  if Size(RecSetwise(pcode,RecNamesInt(pcode)))>d then
    #Display("first itrn, depth =");
    #Print(d);
    #Print(pcode);veclist,pcode,d,Asets,nvars,ssize
    rlist:=certsearch_sss_prover(veclist,ShallowCopy(pcode),d+1,Asets,nvars,svec);
    ret:=rlist[1];
    pcode1:=rlist[2];
  fi;
  if ret=true then
    return [true,pcode1];
  else
    if d+1 in RecNamesInt(pcode) then
      lex_pivot:=pcode.(d+1);
    else
      lex_pivot:=1;
    fi;
    # clean pcode
    for k in RecNamesInt(pcode) do
      if k>d+1 then
        Unbind(pcode.(k));
      fi;
    od;
    lexvars:=[lex_pivot..nvars];
    defvars:=RecSetwise(pcode,RecNamesInt(pcode));
    SubtractSet(lexvars,defvars);
    #Display (["def",defvars,"lex",lexvars]);
    for v in lexvars do
      pcode.(d+1):=v;
      #if Size(veclist) = 9 then
      #Display(["try mapping",d+1,v]);
      #fi;
      if testcons_ss(veclist,ShallowCopy(pcode),Asets,svec,v) = true then
        #defn worked
        if Size(RecSetwise(pcode,RecNamesInt(pcode)))=Size(veclist) then # we're finished
          #Display(["depth",d,"newdef",v,"defvars",defvars,"pcodedefs",RecSetwise(pcode,RecNamesInt(pcode)),"veclist size",Size(veclist),"defvarssize",Size(defvars)+1,"npcodedefs",Size(RecSetwise(pcode,RecNamesInt(pcode)))]);
          return [true,pcode];
        else
          # go deeper in the tree
          #Display(["Defined",defvars+1,"going deeper"]);
          rlist:=certsearch_sss_prover(veclist,ShallowCopy(pcode),d+1,Asets,nvars,svec);
          if rlist[1]=true then
            return [true,rlist[2]];
          fi;
        fi;
      else
        # defn didn't work
        Unbind(pcode.(d+1));
      fi;
    od;
    #Display("********Search failed*********");
    return [false,pcode];
  fi;
end);

InstallGlobalFunction(idmap,
function(n)
  local x,i;
  x:=rec();
  for i in [1..n] do
    x.(i):=i;
  od;
  return x;
end);


InstallGlobalFunction(Leiterspiel_allpoly,
function(K,F,max_simple,coderank)
   local O, OrbitTrans, StabMap,init_rlist, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,goodpoly,G,D,A,AonSets,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple,loopy,trlist;;

   if not IsPrimeField(F) then
     G:=CollineationGroup(ProjectiveSpace(coderank-1,Size(F)));#GL(d,Size(F));
     A:= OnSubspaceByCollineation;#OnSubspacesByCanonicalBasis;
     AonSets:= OnSetOfSubspacesByCollineation;#OnSetOfSubspacesByCanonicalBasis;
     D:=ListOfSubspaces2VectorRep(baseskd_list(Size(F),coderank,[K]));
   else
     G:=GL(coderank,Size(F));
     A:= OnSubspacesByCanonicalBasis;
     AonSets:= OnSetOfSubspacesByCanonicalBasis;
     D:=baseskd_list(Size(F),coderank,[K]);
   fi;

   O:=OrbitsDomainSorted(G,D,A);
   # List of Lists storing transversals
   OrbitTrans:=EmptyPlist(Size(D));
   OrbitTrans[1]:=[];
   StabMap:=EmptyPlist(Size(D));
   StabMap[1]:=[];
   transMap:=EmptyPlist(Size(D));
   # list of maps with map at index i serving as validity certificate of OrbitTrans[subsSize][i]
   for i in [1..Size(O)] do
      OrbitTrans[1][i]:=[O[i][1]];
      StabMap[1][i]:=Stabilizer(G,OrbitTrans[1][i][1],A);
   od;
   psi:=[];
   phiR:=[];
   search_success:=true;
   # enumerate incrementally in subsSize
   for subsSize in [1..max_simple-1] do
    tempPcodeList:=[];
    StabMap[subsSize+1]:=[];
    OrbitTrans[subsSize+1]:=[];
    if Size(OrbitTrans[subsSize])=0 then
     break;
    fi;
    transR:=[];
    phiR[subsSize]:=[];
    stabR:=[];
    for i in [1..Size(OrbitTrans[subsSize])] do
    # calculate the transversal and transporter
     transR[i]:=[];
     phiR[subsSize][i]:=[];
     stabR[i]:=[];
     tempOrbs:=OrbitsDomainSorted(StabMap[subsSize][i],Difference(D,OrbitTrans[subsSize][i]),A);
     for j in [1..Size(tempOrbs)] do
      transR[i][j] := tempOrbs[j][1];
      stabR[i][j] := Stabilizer(StabMap[subsSize][i],transR[i][j],A);
      for k in [1..Size(tempOrbs[j])] do
       l:=Position(D,tempOrbs[j][k]);
       phiR[subsSize][i][l]:=RepresentativeAction(StabMap[subsSize][i],tempOrbs[j][k],tempOrbs[j][1],A);
      od;
     od;
    od;
    psi[subsSize]:=EmptyPlist(Size(OrbitTrans[subsSize]));
    for i in [1..Size(OrbitTrans[subsSize])] do
     psi[subsSize][i]:=EmptyPlist(Size(D));
     for j in [1..Size(D)] do
      psi[subsSize][i][j]:=[];
     od;
    od;
    curLoc:=1;
    #for each set R in the transversal
    for i in [1..Size(OrbitTrans[subsSize])] do
     R:=OrbitTrans[subsSize][i];

     # for each x to augment it with
     for j in [1..Size(transR[i])] do
      lj:=Position(D,transR[i][j]);
      #Display(["Test x="]);
      if Size(psi[subsSize][i][lj])=0 then
        # this was undefined, so go here
        x:=transR[i][j];
        Rux:=ShallowCopy(R);
        Append(Rux,[x]);

        H:=stabR[i][j];
        #caculate initial orbit under H in R
        if Size(R)>1 then
          rl:=OrbitsDomainSorted(H,R,A);
        else
          rl:=[R];
        fi;
        for ri in [1..Size(rl)] do
          r:=rl[ri][1];
          Rmrux:=Concatenation(Difference(R,[r]),[x]);
          Sort(Rmrux);
          # find the transporter for Rmrux
          trlist:=transportMapLazy(Rmrux, D, A, AonSets, phiR, psi, transMap, OrbitTrans,G);
          t:=trlist[1];
          transMap:=trlist[2];
          S:=AonSets(Rmrux,t);
          # S is now canonical representative
          tr:=A(r,t);
          lS:=SortedPosition(OrbitTrans[subsSize],S,4);
          if not lS=fail then
            ltr:=SortedPosition(D,tr,2);
            h:=phiR[subsSize][lS][ltr];
            y:=A(tr,h);
            ly:=SortedPosition(D,y,2);
            if S=R and x=y then
            # we found a new group element of H
            H:=ClosureGroup(H,t*h);
              #gap uses a right group action
            else
              psi[subsSize][lS][ly]:=[Inverse(t*h)];
            fi;
          fi;
        od;
        #Display(["i'",i,tempPcodeList]);
        Append(OrbitTrans[subsSize+1],[Rux]);
        StabMap[subsSize+1][curLoc]:=H;
        curLoc:=curLoc+1;
        #Display(["i''",i,tempPcodeList]);
      fi;
     od;
    od;
   od;
   goodpoly:=EmptyPlist(Size(OrbitTrans)); #transversal elements with required rank
   for j in [1..Size(OrbitTrans)] do
    goodpoly[j]:=[];
     for i in [1..Size(OrbitTrans[j])] do
       # keep only the simple codes satisfying rank=d condition
       if coderank=SubRankMat_vec(OrbitTrans[j][i],[1..j]) then
        Append(goodpoly[j],[OrbitTrans[j][i]]);
       fi;
     od;
   od;
   return goodpoly;
end);
