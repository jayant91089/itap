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
if not IsBound(set2int) then
set2int:=function(s)
  local i,j;
  i:=0;
  for j in s do
    i:=i+2^(Int(j)-1);
  od;
  return i;
end;
fi;

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
    cons:=[[[1,2,3,4],[1,2,3,4,5]],[[1,2,5],[1,2,5,6]],[[2,3,6],[2,3,6,7]],[[3,4,7],[3,4,7,8]],[[4,6,8],[2,4,6,8]],[[2,3,4,8],[1,2,3,4,8]],[[1,4,5,8],[1,2,4,5,8]],[[1,4,5,8],[1,3,4,5,8]],[[1,2,3,7],[1,2,3,4,7]],[[1,5,7],[1,3,5,7]]];
    return [cons,nsrc,nvars];
  end);

InstallGlobalFunction(U2kNet,
  function(k)
    local cons,nsrc,nvars,i,p;
    nvars:=k;
    nsrc:=2;
    cons:=[];
    for i in [2..k-1] do # msg creation constraints
      Append(cons,[[[1,i],[1,i,i+1]]]);
    od;
    Append(cons,[[[1,k],[1,2,k]]]); # decoding constraint for source 2
    for p in Combinations([2..k],2) do
      Append(cons,[[[p[1],p[2]],[1,p[1],p[2]]]]); # decoding constraints for source 1
    od;
    return [cons,nsrc,nvars];
  end);

InstallGlobalFunction(ButterflyNet,
  function()
    return U2kNet(3);
  end);

InstallGlobalFunction(BenalohLeichter,
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

if not IsBound(RecSetwise) then
RecSetwise:=function(r,s)
  # access a record setwise
  local k,l;
  l:=[];
  for k in s do
    Append(l,[r.(k)]);
  od;
  return l;
end;
fi;

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

if not IsBound(RecNamesInt) then
RecNamesInt:=function(r)
  # Returns all values in a record
  local i,intnames;
  intnames:=[];
  for i in RecNames(r) do
   Append(intnames,[Int(i)]);
  od;
  return intnames;
end;
fi;

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
  gl:=GL(d,Size(F));
  A:= OnSubspacesByCanonicalBasis;
  AonSets:= OnSetOfSubspacesByCanonicalBasis;
  D:=baseskd(Size(F),d,k);
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

if not IsBound(DeepSort) then
DeepSort:=function(list,nlevels,l)
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
end;
fi;


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
  rlist:=findrep(rankvec,nvars,F,d,klist,nsimple,[lazy]);
  if rlist[1]=true then
    return rlist;
  else
    return [false];
  fi;
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
  local d,cons,nsrc,nvars,rlist,i,min_simple,max_simple,nsimple,lazy,k, min_simple_default;
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
  min_simple_default:=0;
  for i in [1..nsrc] do
    if rvec[i]>0 then
      min_simple_default:=min_simple_default+1;
    fi;
  od;
  if Size(optargs)=0 then
    min_simple:=min_simple_default;
    max_simple:=nvars;
  else
    if IsBound(optargs[1]) then
      min_simple:=optargs[1];
      max_simple:=optargs[1];
    else
      min_simple:=min_simple_default;
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
    gl:=GL(d,Size(F));
    #Display(gl);
    A:= OnSubspacesByCanonicalBasis;
    AonSets:= OnSetOfSubspacesByCanonicalBasis;
    D:=baseskd_list(Size(F),d,klist);
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

# Subramanian-Thangaraj (groebner)
InstallGlobalFunction(TopSort,
function(dag)
local nb_O,nb_I,I,O,N,Nx,v,e,torder,V,E;
V:=dag[1];
E:=dag[2];
nb_O:=rec();
nb_I:=rec();
N:=rec();
for v in V do
  nb_I.(v):=0;
  nb_O.(v):=0;
od;
I:=rec();
O:=rec();
for v in V do
  I.(v):=[];
  O.(v):=[];
  for e in E do
    if v=e[1] then # v is tail
      nb_O.(v):=nb_O.(v)+1;
      Append(O.(v),[e]);
    fi;
    if v=e[2] then # v is head
      nb_I.(v):=nb_I.(v)+1;
      Append(I.(v),[e]);
    fi;
  od;
  N.(v):=Size(O.(v));
od;
torder:=[];
Nx:=ShallowCopy(N);
for v in V do
  if N.(v)=0 then
    Append(torder,[v]);
    Nx.(v):=-1;
    for e in I.(v) do
      Nx.(e[1]):=Nx.(e[1])-1;
    od;
  fi;
od;
while not Size(torder)=Size(V) do
  #Display(Nx);
  for v in V do
    if Nx.(v)=0 then
      break;
    fi;
  od;
  #Display(v);
  for e in I.(v) do
    Nx.(e[1]):=Nx.(e[1])-1;
  od;
  Append(torder,[v]);
  Nx.(v):=-1;
od;
return [torder,I,nb_I,O,nb_O];
end);

if not IsBound(DeepCopy_lol) then
DeepCopy_lol:=function(lol)
  local olol,l;
  olol:=[];
  for l in lol do
  Append(olol,[ShallowCopy(l)]);
  od;
  return olol;
end;
fi;

InstallGlobalFunction(DeepCopy_rec,
function(r)
  local ro,i;
  ro:=rec();
  for i in RecNamesInt(r) do

    ro.(i):=DeepCopy_lol(r.(i));
  od;

  return ro;
end);

InstallGlobalFunction(Addnode2,
function(dagstruct,Ix,ci,Ox,co)
# Addnode for colored edges
# ci and co are lists giving colors of respective edges
  local V,E,I,O,x,i,o,nb_I,nb_O,j,k;
  V:=ShallowCopy(dagstruct[1]);
  E:=DeepCopy_lol(dagstruct[2]);
  I:=DeepCopy_rec(dagstruct[3]);
  O:=DeepCopy_rec(dagstruct[5]);
  nb_I:=ShallowCopy(dagstruct[4]);
  nb_O:=ShallowCopy(dagstruct[6]);
  x:=Maximum(V)+1;
  Append(V,[x]);
  I.(x):=[];
  O.(x):=[];
  nb_I.(x):=Size(Ix);
  nb_O.(x):=Size(Ox);

  for j in [1..Size(Ix)] do
    i:=Ix[j];
    Append(I.(x),[[i,x,ci[j]]]);
    Append(E,[[i,x,ci[j]]]);
    Append(O.(i),[[i,x,ci[j]]]);
    nb_O.(i):=nb_O.(i)+1;
  od;
  for k in [1..Size(Ox)] do
    o:=Ox[k];
    Append(O.(x),[[x,o,co[k]]]);
    Append(E,[[x,o,co[k]]]);
    Append(I.(o),[[x,o,co[k]]]);
    nb_I.(o):=nb_I.(o)+1;
  od;
  return [V,E,I,nb_I,O,nb_O];
end);



InstallGlobalFunction(Delnode,
function(dagstruct,x)
# color safe
  local V,E,I,O,nb_I,nb_O,i,o,e;
  V:=ShallowCopy(dagstruct[1]);
  E:=DeepCopy_lol(dagstruct[2]);
  I:=DeepCopy_rec(dagstruct[3]);
  O:=DeepCopy_rec(dagstruct[5]);
  nb_I:=ShallowCopy(dagstruct[4]);
  nb_O:=ShallowCopy(dagstruct[6]);
  Remove(V,Position(V,x));
  for e in I.(x) do
    Remove(E,Position(E,e));
    Remove(O.(e[1]),Position(O.(e[1]),e));
    nb_O.(e[1]):=nb_O.(e[1])-1;
  od;
  Unbind(I.(x));
  Unbind(nb_I.(x));
  for e in O.(x) do
    Remove(E,Position(E,e));
    Remove(I.(e[2]),Position(I.(e[2]),e));
    nb_I.(e[2]):=nb_I.(e[2])-1;
  od;
  Unbind(O.(x));
  Unbind(nb_O.(x));
  return [V,E,I,nb_I,O,nb_O];
end);

InstallGlobalFunction(NC2dagstruct,
function(NC)
local rlist,dagstruct;
rlist:=TopSort(NC[1]);
dagstruct:= [ShallowCopy(NC[1][1]),ShallowCopy(NC[1][2])];
Append(dagstruct,rlist{[2..Size(rlist)]});
return dagstruct;
end);

InstallGlobalFunction(IsClawmember,
function(t,T,ds)
local tparents,e,p,sib,esib;
  tparents:=[];
  for e in ds[3].(t) do
    Append(tparents,[e[1]]);
  od;
  tparents:=AsSet(tparents);
  if Size(tparents)=1 then
    # sanity check the single parent of t
    p:=tparents[1];
    for e in ds[5].(p) do
      if not e[2] in T then
        return false;
      else
        sib:=e[2];
        for esib in ds[3].(sib) do
          if not esib[1]=p then
            return false;
          fi;
        od;
      fi;
    od;
    return true;
  else
    return false;
  fi;
end);

InstallGlobalFunction(NCinstance2dag2,
function(NCinstance,rvec)
local cons,nsrc,nvars,S,T,V,g,Edges,msg2node,i,curnode,usedcons,ip,goodcon,c,io,o,opmsg,msg,dnode,se,usedT,
NCr1,ds,newV,newE,newS,newT,newg,Ecolors,src2nodes,node2src,e,ex,v,vp,t,gt,rvp,gvp,vpe,sv,x,gvpe,elist;
  cons:=NCinstance[1];
  nsrc:=NCinstance[2];
  nvars:=NCinstance[3];
  elist:=[];
  S:=[1..nsrc]; # sources
  T:=[]; # sinks
  V:=[1..nsrc]; # nodes
  g:=[]; # demands
  curnode:=nsrc+1;
  Edges:=[];
  msg2node:=rec();
  for  i in [1..nsrc] do
    msg2node.(i):=i;
  od;
  curnode:=nsrc+1;
  usedcons:=[];
  while Size(RecNamesInt(msg2node))<nvars do
    # find a constraint whose input msgs have nodes defined
    for c in cons do
    if not c in usedcons then
      ip:=ShallowCopy(c[1]);
      goodcon:=true;
      for i in ip do
        if not IsBound(msg2node.(i)) then
          goodcon:=false;
          break;
        fi;
      od;
      if goodcon=true then
        Append(usedcons,[c]);
        #Display(c);
        #Display([V,Edges]);
       # add nodes where op msgs are created
       io:=SortedList(ShallowCopy(c[2]));
       #Display(["io",io]);
       SubtractSet(io,c[1]);
       o:=io;
       #Display(["o",o]);
       if not IsSubset([1..nsrc],o) then
          #Display(["o",o]);
         for opmsg in o do
          #Display(["define for msg",opmsg]);
          Append(V,[curnode]);
          for msg in c[1] do
            Append(Edges,[[msg2node.(msg),curnode]]);
          od;
          #Display(["curnode b4",curnode]);
          curnode:=curnode+1;
          Append(V,[curnode]);
          Append(Edges,[[curnode-1,curnode]]);
          Append(elist,[[curnode-1,curnode]]);
          msg2node.(opmsg):=curnode;
          curnode:=curnode+1;
          #Display(["curnode after",curnode]);
         od;
        else # decoder constraint
          #Display(["deccon",c]);
          Append(V,[curnode]); # decoder
          for msg in c[1] do
            Append(Edges,[[msg2node.(msg),curnode]]);
          od;
          dnode:=curnode;
          curnode:=curnode+1;
          if Size(o)>1 then
            for opmsg in o do
              Append(V,[curnode]);
              Append(Edges,[[dnode,curnode]]);
              Append(T,[curnode]);
              Append(g,[[opmsg]]);
              curnode:=curnode+1;
            od;
          else
            Append(T,[dnode]);
            Append(g,[[o[1]]]);
          fi;
        fi;
      fi;
    fi;
    od;
  od;
  NCr1:=[[V,Edges],S,T,g];
  ds:=NC2dagstruct(NCr1);
  newV:=ShallowCopy(V);
  curnode:=Maximum(V)+1;
  newE:=DeepCopy_lol(Edges); # a multiset
  newS:=ShallowCopy(S);
  newg:=[];
  Ecolors:=[]; # gives integer color of an edge
  src2nodes:=rec();
  for msg in [1..nsrc] do
    src2nodes.(msg):=[];
  od;
  node2src:=rec();
  # fix r>1 sources
  for msg in RecNamesInt(msg2node) do
    v:=msg2node.(msg);
    if msg in [1..nsrc] then
      if rvec[msg]>1 then
      # must be fixed
      #Display(["must fix source",msg]);
      Remove(newS,Position(newS,msg));
        for i in [1..rvec[msg]] do
          Append(newV,[curnode]);
          Append(newE,[[curnode,v]]);
          Append(src2nodes.(msg),[curnode]);
          Append(newS,[curnode]);
          curnode:=curnode+1;
        od;
        for i in [2..rvec[msg]] do #for each additional symbol
          for se in ds[5].(msg) do # add an edge in parallel to each o/p edge
            Append(newE,[se]);
          od;
        od;
      else
      # no need to fix
      #Display(["no need to fix source",msg]);
      src2nodes.(msg):=[v];
      fi;
    fi;
  od;
  # fix r>1 edges: add parallel edges
  for msg in RecNamesInt(msg2node) do
    v:=msg2node.(msg);
    if not msg in [1..nsrc] then
      if rvec[msg]>1 then
      #Display(["Fix for msg",msg]);
      # must be fixed
      e:=ds[3].(v)[1]; # the only input edge
      for i in [2..rvec[msg]] do
        Append(newE,[ShallowCopy(e)]);
        Append(elist,[e]);
        #Display(["new edge",e,i]);
      od;

      for e in ds[5].(v) do
        for i in [2..rvec[msg]] do
          #Display(["new edge",e,i]);
          Append(newE,[ShallowCopy(e)]);
        od;
      od;
      fi;
    fi;
  od;
  # new decoders
  newT:=[];
  usedT:=[];
  for i in [1..Size(T)] do
    t:=T[i];
    gt:=g[i];
    #if Size(src2nodes.(gt[1])) >1 then #
      if t in newV and not t in usedT then # has this been removed already?
        #Display(["fix for dec",t]);
        rvp:=IsClawmember(t,T,ds);
        if rvp=true then # revamp vp
          vp:=ds[3].(t)[1][1];
          # Remove output edges and nodes of vp
          #Display(["fix parent",vp]);
          gvp:=[];
          for vpe in ds[5].(vp) do
            gvpe:=g[Position(T,vpe[2])];
            if rvec[gvpe[1]]>1 then
            Append(gvp,gvpe);
            Remove(newV,Position(newV,vpe[2]));
            Remove(newE,Position(newE,vpe));
            #Display(["Remove",vpe,vpe[2]]);
            Append(usedT,[vpe[2]]);
            else
              Append(newT,[vpe[2]]);
              Append(newg,[g[Position(T,vpe[2])]]);
              #Display(["Spare (rate 1)",vpe,vpe[2]]);
              Append(usedT,[vpe[2]]);
            fi;
          od;
          # Add new decoders
          for sv in gvp do
            for x in src2nodes.(sv) do
              Append(newV,[curnode]);
              Append(newE,[[vp,curnode]]);
              Append(newT,[curnode]);
              Append(newg,[[x]]);
              #Display(["Newdec",curnode,x]);
              curnode:=curnode+1;
            od;
          od;
        else
          #Display(["fix t itself",t]);
          # it is a single demand dec
          Append(usedT,[t]);
          if rvec[g[i][1]]>1 then # must add new nodes
            for x in src2nodes.(g[i][1]) do
              Append(newV,[curnode]);
              Append(newE,[[t,curnode]]);
              Append(newT,[curnode]);
              Append(newg,[[x]]);
              #Display(["Newdec",curnode,x]);
              curnode:=curnode+1;
            od;
          else
            #Display(["only rate 1 demand, no fixing for",t]);
            Append(newT,[t]);
            Append(newg,[[g[i][1]]]);
          fi;
        fi;
      fi;
    #fi;
  od;
  return [[[newV,newE],newS,newT,newg],elist];
end);

InstallGlobalFunction(ForestTransform2,
function(NC)
# for colored edges
# NC is a dag_NCinstance NC[1]=dag,NC[2]=S,NC[3]=T,NC[4]=g (list)
# ds[1]=V, ds[2]=E,ds[3]=I,ds[4]=nb_I,ds[5]=O,ds[6]=nb_O
  local torder,rlist,ds,ds1,copymap,newv,v,e,Ix,ex,t,ci,co;
  rlist:=TopSort(NC[1]);
  torder:=rlist[1];
  ds:=NC2dagstruct(NC);
  copymap:=rec(); # record saying whose copy is which node in the new graph
  newv:=Maximum(ds[1])+1;
  for v in torder do
    if ds[6].(v)>1 then
      #Display(Concatenation("Replicate ",String(v)));
      ds1:=ds;
      for e in ds[5].(v) do
        #Display(Concatenation("Copy for ",String(e)));
        Ix:=[];
        ci:=[];
        for ex in ds1[3].(v) do
          Append(Ix,[ex[1]]); # each input edge gets color of ex
          Append(ci,[ex[3]]);
        od;
        ds1:=Addnode2(ds1,Ix,ci,[e[2]],[e[3]]); # o/p edge gets color of e
        #Display(ds1[4]);
        copymap.(newv):=v;
        newv:=newv+1;
      od;
      #Display(Concatenation("I/O Before = ", String(ds1[3].(v))," ", String(ds1[5].(v))));
      ds1:=Delnode(ds1,v);
      ds:=ds1;
      #Display(Concatenation("I/O After = ", String(ds1[3].(v))," ", String(ds1[5].(v))));
    fi;
  od;
  for t in NC[3] do
    copymap.(t):=t;
  od;
  return [ds,copymap];
end);

InstallGlobalFunction(NC2colors,function(NC)
local E,Ecolors,Eset,pos,i,e;
E:=NC[1][2];
Ecolors:=EmptyPlist(Size(E));
Eset:=AsSet(E);
for e in Eset do
  pos:=Positions(E,e);
  for i in [1..Size(pos)] do
    Ecolors[pos[i]]:=i;
  od;
od;
return Ecolors;
end);

InstallGlobalFunction(ColorEdges,
function(Edges)
local Ecolors,Eset,pos,i,e,ce;
Ecolors:=EmptyPlist(Size(Edges));
Eset:=AsSet(Edges);
for e in Eset do
  pos:=Positions(Edges,e);
  for i in [1..Size(pos)] do
    Ecolors[pos[i]]:=i;
  od;
od;
ce:=DeepCopy_lol(Edges);
for i in [1..Size(Edges)] do
  Append(ce[i],[Ecolors[i]]);
od;
return ce;
end);

InstallGlobalFunction(NC2coloredNC,
function(NC)
local Ecolors,i,CNC;
Ecolors:=NC2colors(NC);
CNC:=EmptyPlist(4);
CNC[1]:=EmptyPlist(2);
CNC[1][1]:=ShallowCopy(NC[1][1]);
CNC[1][2]:=DeepCopy_lol(NC[1][2]);
CNC[2]:=ShallowCopy(NC[2]);
CNC[3]:=ShallowCopy(NC[3]);
CNC[4]:=ShallowCopy(NC[4]);
for i in [1..Size(NC[1][2])] do
  Append(CNC[1][2][i],[Ecolors[i]]);
od;
return CNC;
end);



InstallGlobalFunction(IsReachable,
function(ds,c,v)
  # Is c --> v?
  local curnode;
  curnode:=c;
  while not curnode=v and not ds[6].(curnode)=0  do# while we reach either a sink or v
    curnode:=ds[5].(curnode)[1][2];
  od;
  if curnode=v then
  return true;
  else
  return false;
  fi;
end);

InstallGlobalFunction(sinkid,
function(NC,ds,v)
local s;
  for s in NC[3] do
    if IsReachable(ds,v,s) then
      return s;
    fi;
  od;
  return 0;
end);

InstallGlobalFunction(EdgeComp2,
function(e,NC,ds,a,scopy2var,copymap,vl)
  # requires colored edges
  # e is in original graph find its copies
  local ecopies,ec_sinkid,ec,coeffs,ecoeffs,nsrc,s,t,ecpairs,srcpairs,ecpair,srcpair,epolylist,p,i,j,elist;
  nsrc:=Size(NC[2]);
  ecopies:=[];
  ec_sinkid:=[]; # sink of each copy
  for ec in ds[2] do
    if copymap.(ec[1])=e[1] and copymap.(ec[2])=e[2] and ec[3]=e[3] then
      Append(ecopies,[ec]);
    fi;
  od;
  if not Size(ecopies)>0 then
    return [];
  fi;
  coeffs:=[]; # list of records of each edge's coefficients
  for i in [1..Size(ecopies)] do
    ecoeffs:=rec();
    for j in NC[2] do
      ecoeffs.(j):=0;
    od;
    Append(coeffs,[ecoeffs]);
  od;
  # find coeffs of each source in each tree
  for ec in ecopies do
    t:=sinkid(NC,ds,ec[1]); # tree in which ec lives
    for s in RecNamesInt(scopy2var) do
      #Display(["Test source ",s,copymap.(s), "in tree", t]);
      if IsReachable(ds,s,ec[1]) then # include s's coeff in coeffs
      #Display(["e carries ", copymap.(s), "in tree", t  ]);
        ecoeffs:=coeffs[Position(ecopies,ec)];
        ecoeffs.(copymap.(s)):=ecoeffs.(copymap.(s))+a[scopy2var.(s)];
        coeffs[Position(ecopies,ec)]:=ecoeffs;
      fi;
    od;
  od;
ecpairs:=Combinations(ecopies,2);
srcpairs:=Combinations(NC[2],2);
#srcpairs:=Combinations([1..nsrc],2);
epolylist:=[];
for ecpair in ecpairs do
  #if not sinkid(NC,ds,ecpair[1][1])=sinkid(NC,ds,ecpair[2][1]) then
    for srcpair in srcpairs do
      if not coeffs[Position(ecopies,ecpair[1])].(srcpair[1])=0 and not coeffs[Position(ecopies,ecpair[2])].(srcpair[1])=0 then
        if not coeffs[Position(ecopies,ecpair[1])].(srcpair[2])=0 and not coeffs[Position(ecopies,ecpair[2])].(srcpair[2])=0 then
          p:=coeffs[Position(ecopies,ecpair[1])].(srcpair[1])*coeffs[Position(ecopies,ecpair[2])].(srcpair[2])-coeffs[Position(ecopies,ecpair[2])].(srcpair[1])*coeffs[Position(ecopies,ecpair[1])].(srcpair[2]);
          Append(epolylist,[p]);
        fi;
      fi;
    od;
  #fi;
od;
if vl>0 then
  Display(["Edge compatiblity conditions for ", e," = ", Size(epolylist)]);
  Display(epolylist);
fi;
return epolylist;
end);

InstallGlobalFunction(IsSolvableNC2,
function(NC,ds,copymap,F,elist,vl)
# requires NC, ds and elist to have colored edges
local varlist,scopy2var,varid,v,PR,a,polylist,s,p,c,v1,v2,s1,s2,plhs,prhs,plhs1,plhs2,prhs1,prhs2,hf1,hf2,hf3,hf4,h,t,vp,pairs,goodlist,spairs,sp,I,e,nb_noi,nb_ec;
varlist:=[];
scopy2var:=rec(); # map leafs to variables
varid:=1;
for v in ds[1] do
  if ds[4].(v)=0 then # leafs
    Append(varlist,[Concatenation("a",String(v))]);
    scopy2var.(v):=varid;
    varid:=varid+1;
  fi;
od;
PR:=PolynomialRing(F,varlist);
a:=IndeterminatesOfPolynomialRing( PR );;
if vl>0 then
  Display(Concatenation("There are ",String(Size(a))," path gain variables."));
fi;
polylist:=[];
for v in ds[1] do # for each vtx
  if ds[6].(v)=0 then # if it is a sink copy
    for s in NC[2] do # for each source
      p:=0;
      for c in ds[1] do # for each copy
        if IsBound(copymap.(c)) and copymap.(c)=s and IsReachable(ds,c,v) then# id it is a copy of s and reaches v
          # add c's variable to p
          p:=p+a[scopy2var.(c)];
        fi;
      od;
      # add 0 or 1 based on whether s is needed

      if not p=0 then
        if s in NC[4][Position(NC[3],copymap.(v))] then
         p:=p-1;
        fi;
        Append(polylist,[p]);
      fi;
    od;
  fi;
od;
nb_noi:=Size(polylist);
#Display(["Nointerference =",Size(polylist)]);
for e in elist do
  Append(polylist,EdgeComp2(e,NC,ds,a,scopy2var,copymap,vl-1));
od;
nb_ec:=Size(polylist)-nb_noi;
if vl>0 then
  Display(Concatenation("No-Interference (",String(nb_noi),") + Edge-Compatibility (",String(nb_ec), ") = ",String(Size(polylist)), " polynomials." ));
fi;
#Display(["EdgeComp =",Size(polylist)]);
#Display(goodlist);
# Append field related conditions to polylist
for v in a do
  Append(polylist,[v^Size(F)-v]);
od;
I:=Ideal(PR,polylist);
#Display(HasTrivialGroebnerBasis(I));
if vl>1 then
  Display(["Groebner Basis:",GroebnerBasis(I)]);
fi;
return [not HasTrivialGroebnerBasis(I),GroebnerBasis(I)];
end);

InstallGlobalFunction(proverate_groebner,
function(ncinstance,rvec,F,optargs)
  local NC,CNC,ds,copymap,elist,rlist,vl;
  if Size(optargs)>0 then
    vl:=optargs[1];
  else
    vl:=0;
  fi;
  if vl>0 then
    Display("Constructig DAG...");
  fi;
  rlist:=NCinstance2dag2(ncinstance,rvec);
  NC:=rlist[1];
  elist:=rlist[1][1][2];
  elist:=ColorEdges(elist);
  CNC:=NC2coloredNC(NC);
  if vl>0 then
    Display(Concatenation("DAG has ",String(Size(CNC[1][1]))," vertices and ",String(Size(CNC[1][2])), " edges."));
    Display("Constructig forest...");
  fi;
  rlist:=ForestTransform2(CNC);
  ds:=rlist[1];
  copymap:=rlist[2];
  if vl>0 then
    Display(Concatenation("The forest has ",String(Size(ds[1]))," vertices and ",String(Size(ds[2])), " edges."));
  fi;
  #Display(["field",F]);
  return IsSolvableNC2(CNC,ds,copymap,F,elist,vl);
end);


# rate region computation using lrs
if not IsBound(skipline) then
skipline:=function(str,i)
local j;
if i>Size(str) or i<0 then
  return -1;
fi;
for j in [i..Size(str)] do
  if str[j]='\n' then
    if j=Size(str) then
      return -1;
    else
      return j+1;
    fi;
  fi;
od;
return -1;
end;
fi;

if not IsBound(nextnum) then
nextnum:=function(str,i)
local foundnum, j,k,isneg;
if i>Size(str) or i<0 then
  return -1;
fi;
foundnum:=false;
isneg:=false;
for j in [i..Size(str)] do
  if not str[j]=' ' then
    if IsDigitChar(str[j]) then
      if j-1>=1 and str[j-1]='-' then
        isneg:=true;
      fi;
      foundnum:=true;
      break;
    fi;
  fi;
od;
if foundnum=false then
 return [false,-1,-1]; # [found?, number, next_i]
fi;
for k in [j+1..Size(str)] do
  if not IsDigitChar(str[k]) then
    break;
  fi;
od;
if isneg=true then
  return [true,Int(str{[j-1..k-1]}),k];
else
  return [true,Int(str{[j..k-1]}),k];
fi;
end;
fi;


InstallGlobalFunction(Readextfile,
function(fname)
local input,str,k,mtx,vec,j,vecstr,pos,rlist;
input := InputTextFile(fname);;
str:=ReadAll(input);
CloseStream(input);
k:=1;
while not k=-1 do
  if not k+4>Size(str) then
    if not str{[k..k+4]}="begin" then
      k:=skipline(str,k);
    else
      break;
    fi;
  else
    return []; # no matrix in the file
  fi;
od;
mtx:=[];
k:=skipline(str,k);
k:=skipline(str,k);
if k=-1 then
  return mtx;
fi;
while not str{[k..k+2]}="end" do
  vec:=[];
  j:=skipline(str,k);
  vecstr:=str{[k..j-1]};
  pos:=1;
  while not pos=-1 do
    rlist:=nextnum(vecstr,pos);
    if rlist[1]=false then
      break;
    fi;
    Append(vec,[rlist[2]]);
    pos:=rlist[3];
  od;
  Append(mtx,[vec]);
  k:=j;
  if k=-1 then
    return mtx;
  fi;
od;
return mtx;
end);

if not IsBound(writeinefile) then
writeinefile:=function(fname,lin,mtx)
local ostr,row,i,r;
ostr:="";
if Size(lin)=0 then
  ostr:=Concatenation(ostr,"H-representation\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
else
  ostr:= Concatenation(ostr,"H-representation\n","linearity ");
  for r in lin do
      ostr:=Concatenation(ostr,String(r)," ");
  od;
  ostr:=Concatenation(ostr,"\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
fi;
for i in [1..Size(mtx)] do
    row:=mtx[i];
    #ostr:=Concatenation(ostr,"0 ");
    for r in row do
        ostr:=Concatenation(ostr,String(r)," ");
    od;
    ostr:=Concatenation(ostr,"\n");
od;
ostr:=Concatenation(ostr,"end");
PrintTo(fname,ostr);
end;
fi;

InstallGlobalFunction(Readinefile,
function(fname)
local input,str,k,mtx,vec,j,vecstr,pos,rlist,lin,haslin;
input := InputTextFile(fname);;
str:=ReadAll(input);
CloseStream(input);
k:=1;
lin:=[];
haslin:=false;
while not k=-1 do
  #Display(["linloop ",k]);
  if not k+8>Size(str) then
    if not str{[k..k+8]}="linearity" then
      k:=skipline(str,k);
    else
      haslin:=true;
      break;
    fi;
  else
    break;
  fi;
od;
if haslin=true then
  lin:=[];
  j:=skipline(str,k);
  vecstr:=str{[k+9..j-1]};
  pos:=1;
  while not pos=-1 do
    rlist:=nextnum(vecstr,pos);
    if rlist[1]=false then
      break;
    fi;
    Append(lin,[rlist[2]]);
    pos:=rlist[3];
  od;
fi;
k:=1;
while not k=-1 do
  #Display(["begloop ",k]);
  if not k+4>Size(str) then
    if not str{[k..k+4]}="begin" then
      k:=skipline(str,k);
    else
      break;
    fi;
  else
    return [[],[]]; # no matrix in the file
  fi;
od;
mtx:=[];
k:=skipline(str,k);
k:=skipline(str,k);
if k=-1 then
  return mtx;
fi;
while not str{[k..k+2]}="end" do
#Display(["endloop ",k]);
  vec:=[];
  j:=skipline(str,k);
  vecstr:=str{[k..j-1]};
  pos:=1;
  while not pos=-1 do
    rlist:=nextnum(vecstr,pos);
    if rlist[1]=false then
      break;
    fi;
    Append(vec,[rlist[2]]);
    pos:=rlist[3];
  od;
  Append(mtx,[vec]);
  k:=j;
  if k=-1 then
    return [lin,mtx];
  fi;
od;
return [lin,mtx];
end);

InstallGlobalFunction(rrcompute,
function(rays,nsrc,nvars,lrs_path)
local ray,f1name,f2name,f3name,f4name,rlist,lin,mtx,new_mtx,row,i,rays2,projrays,temp_dir,conineq,f5name,f6name,j;
#lrs_path:="/home/aspitrg3-users/jayant/lrslib-061/";
temp_dir:=DirectoryTemporary();
f1name:=Filename( temp_dir, "file1.ext" );
f2name:=Filename( temp_dir, "file1red.ext" );
f3name:=Filename( temp_dir, "file2.ine" );
f4name:=Filename( temp_dir, "file3.ine" );
f5name:=Filename( temp_dir, "file4.ine" );
f6name:=Filename( temp_dir, "file5.ine" );

#f4rname:=Filename( temp_dir, "file3.ine" );

for i in [nsrc+1..nvars] do
  Append(rays,[Concatenation(ZeroMutable([1..nsrc]),ZeroMutable([nsrc+1..i]),[1],ZeroMutable([i+1..nvars]))]);
od;
rays2:=[];
for ray in rays do
Append(rays2,[Concatenation(ray{[nsrc+1..nvars]},ray{[1..nsrc]})]);
od;
rays2extfile(f1name,rays2);
Exec(Concatenation(lrs_path,"redund"," ",f1name," ",f2name));;
#rays2:=Readextfile(f2name);
Exec(Concatenation(lrs_path,"lrs"," ",f2name," ",f3name));
rlist:=Readinefile(f3name);
lin:=rlist[1]{[2..Size(rlist[1])]};
mtx:=rlist[2];
new_mtx:=[];
for row in mtx do
  Append(new_mtx,[Concatenation(ZeroMutable([1..Size(row)]),row{[2..Size(row)]})]);
od;
for j in [1..nvars-nsrc] do # edge rate ineq + non-negativity
  conineq:=ZeroMutable([1..2*nvars+1]);
  conineq[1+j]:=1;
  conineq[1+nvars+j]:=-1;
  Append(new_mtx,[conineq]);
  conineq:=ZeroMutable([1..2*nvars+1]);
  conineq[1+j]:=1;
  Append(new_mtx,[conineq]);
od;
for j in [nvars-nsrc+1..nvars] do # src rate ineq
  conineq:=ZeroMutable([1..2*nvars+1]);
  conineq[1+j]:=-1;
  conineq[1+nvars+j]:=1;
  Append(new_mtx,[conineq]);
  conineq:=ZeroMutable([1..2*nvars+1]);
  conineq[1+j]:=1;
  Append(new_mtx,[conineq]);
od;
writeinefile(f4name,lin,new_mtx);
Exec(Concatenation(lrs_path,"lrs"," ",f4name," ",f5name));
mtx:=Readextfile(f5name);
rays2extfile(f6name,mtx{[1..Size(mtx)]}{[2..nvars+1]});
Exec(Concatenation(lrs_path,"lrs"," ",f6name));
end);

InstallGlobalFunction(rrcompute_lrs,
function(rays,nsrc,nvars,lrs_exec)
local ray,f1name,f2name,f3name,f4name,rlist,lin,mtx,new_mtx,row,i,rays2,projrays,temp_dir,f2rname;
#lrs_exec:="/home/aspitrg3-users/jayant/lrslib-061/lrs";
temp_dir:=DirectoryTemporary();
f1name:=Filename( temp_dir, "file1.ext" );
f2name:=Filename( temp_dir, "file2.ine" );
f2rname:=Filename( temp_dir, "file2r.ine" );
f3name:=Filename( temp_dir, "file3.ext" );
f4name:=Filename( temp_dir, "rr.ext" );
rays2extfile(f1name,rays);
Exec(Concatenation(lrs_exec," ",f1name," ",f2name));;
rlist:=Readinefile(f2name);
lin:=rlist[1];
mtx:=rlist[2];
new_mtx:=[];
for row in mtx do
  Append(new_mtx,[Concatenation(ZeroMutable([1..nvars-nsrc]),row)]);
od;
for i in [1..nvars-nsrc] do
  Append(new_mtx,[Concatenation([0],ZeroMutable([1..i-1]),[1],ZeroMutable([1..nvars-nsrc-i]),ZeroMutable([1..nsrc]),ZeroMutable([1..i-1]),[-1],ZeroMutable([1..nvars-nsrc-i]))]);
od;
for i in [1..nvars-nsrc] do
  Append(new_mtx,[Concatenation([0],ZeroMutable([1..i-1]),[1],ZeroMutable([1..nvars-nsrc-i]),ZeroMutable([1..nvars]))]);
od;
writeinefile(f2rname,lin,new_mtx);
Exec(Concatenation(lrs_exec," ",f2rname," ",f3name));;
rays2:=Readextfile(f3name);
projrays:=[];
for ray in rays2 do
Append(projrays,[Concatenation(ray{[nvars-nsrc+1..nvars]},ray{[1..nvars-nsrc]})]);
od;
rays2extfile(f4name,projrays);
Exec(Concatenation(lrs_exec," ",f4name));
end);

InstallGlobalFunction(rays2extfile,
function(fname,rays)
local ostr,ray,i,r;
ostr:=Concatenation("V-representation\nbegin\n",String(Size(rays))," ",String(Size(rays[1])+1), " rational\n");
for i in [1..Size(rays)] do
    ray:=rays[i];
    ostr:=Concatenation(ostr,"0 ");
    for r in ray do
        ostr:=Concatenation(ostr,String(r)," ");
    od;
    ostr:=Concatenation(ostr,"\n");
od;
ostr:=Concatenation(ostr,"end");
PrintTo(fname,ostr);
#return ostr;
end);

InstallGlobalFunction(conichull_lrs,
function(rays,lrs_exec)
local fname;
#lrs_exec:="/home/aspitrg3-users/jayant/lrslib-061/lrs";
fname:=Filename( DirectoryTemporary(), "file.ext" );
rays2extfile(fname,rays);
Exec(Concatenation(lrs_exec," ",fname));
return;
end);


InstallGlobalFunction(LeiterspielWCons_vec_lazy,
function(G,D,A,AonSets,max_simple,netcons,nsrc,nvars,loopy)
   local O, OrbitTrans, StabMap, transMap, k, j, i, subsSize, transR, phiR, stabR, tempOrbs,rpcodes,trlist,
   l, curLoc, R, lj, x, Rux, H, rl, ri, Rmrux, r, t, S, tr, lS, ltr, h, y, ly, psi,PcodeList,tempJointPcodeList,
   rep,tempPcodeList,rlist,apc,nrep,search_success,JointPcodeList,AllCodes,pcodelist1,pcodelist,surviving_simple;
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
      Append(JointPcodeList,[[[OrbitTrans[max_simple][i],PcodeList[i]]]]); # each member of JointPcodeList is a list of non-simple extensions of same simple poly
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
    rpcodes:=[];
    if search_success=true then
      for i in [1..Size(JointPcodeList)] do
        Append(rpcodes,JointPcodeList[i]);
      od;
      return rpcodes;#JointPcodeList;
    else
      return [];
    fi;
   else
    return [];
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
  return LeiterspielWCons_vec_lazy(gl,D,A,AonSets,s,ncinstance[1],ncinstance[2],ncinstance[3],loopy);
end);

InstallGlobalFunction(trivialrates,
function(nsrc,nvars)
local trates,r,i;
trates:=[];
for i in [nsrc+1..nvars] do
    r:=ZeroMutable([1..nvars]);
    r[i]:=1;
    Append(trates,[r]);
od;
return trates;
end);


InstallGlobalFunction(proveregion,
function(ncinstance,k,F,optargs)
  # optargs: []
  #    force_nsimple: boolean that forces the prover to use only the simple codes of specified length,default false
  #    lazy: a boolean indicating whether transporter maps will be evaluated lazily,default true
  local opt_dmax,dlist,d,cons,nsrc,nvars,rlist,i,min_simple,max_simple,nsimple,lazy,allcodes,allrates,apc,code;
  cons:=ncinstance[1];
  nsrc:=ncinstance[2];
  nvars:=ncinstance[3];
  # determine dlist
  if Size(optargs)> 0 then
  	opt_dmax:=optargs[1];
  else
	opt_dmax:=k*nsrc;
  fi;
  dlist:=[1..Minimum(k*nsrc,opt_dmax)];
  lazy:=true;
  allrates:=trivialrates(ncinstance[2],ncinstance[3]); # A list of lists [rvec,parent,map] where parent is index of the code in allcodes
  allcodes:=[];
  apc:=AppCns(cons,nvars);
  for d in dlist do

        min_simple:=d;
        max_simple:=nvars;
        for nsimple in [min_simple..max_simple] do
            #Display(Concatenation("search for","d=",String(d),"nsimple=",String(nsimple)));
            rlist:=veccodegen(ncinstance,F,d,Minimum([d,k]),nsimple,[true]); # rlist is a list containing lists [code,map]
            for code in rlist do
                Append(allrates,certsearch_allrates(code[1],rec(),cons,apc,0,nsrc,nvars));
                allrates:= DuplicateFreeList( allrates );
                Append(allcodes,[code[1]]);
            od;
        od;
  od;
  return [allrates,allcodes];
end);

InstallGlobalFunction(HyperedgeNet1,
function()
return [[[[1,2,3],[1,2,3,4]],[[1,3,4],[1,3,4,5]],[[3,4,5],[3,4,5,6]],[[4,5],[1,3,4,5]],[[4,6],[2,3,4,6]],[[5,6],[2,3,5,6]]],3,6];
end);

InstallGlobalFunction(HyperedgeNet2,
function()
return [[[[1,2,3,5],[1,2,3,4,5]],[[1,3],[1,3,5]],[[3,4,5],[3,4,5,6]],[[4,5],[1,3,4,5]],[[4,6],[2,3,4,6]],[[5,6],[2,3,5,6]]],3,6];
end);

################### Symmetric p-map tree traversal
PermMatGroupF:=function(G,n,F)
  local gens,mgens,g,PMG,pmat, pmatF,r,c,rF;
  gens:=GeneratorsOfGroup(G);
  mgens:=[];
  for g in gens do
    pmat:=PermutationMat(g,n);
    pmatF:=[];
    for r in pmat do
      rF:=[];
      for c in r do
        if c=0 then
          Append(rF,[0*Z(Size(F))]);
        else
          Append(rF,[Z(Size(F))^0]);
        fi;
      od;
      Append(pmatF,[rF]);
    od;
    Append(mgens,[pmatF]);
  od;
  PMG:=GroupByGenerators(mgens);
  return PMG;
end;

PermMatGroupR:=function(G,n)
  local gens,mgens,g,PMG,pmat, pmatF,r,c,rF;
  gens:=GeneratorsOfGroup(G);
  mgens:=[];
  for g in gens do
    pmat:=PermutationMat(g,n);
    pmatF:=[];
    for r in pmat do
      rF:=[];
      for c in r do
        if c=0 then
          Append(rF,[0]);
        else
          Append(rF,[1]);
        fi;
      od;
      Append(pmatF,[rF]);
    od;
    Append(mgens,[pmatF]);
  od;
  PMG:=GroupByGenerators(mgens);
  return PMG;
end;

MatPermutation:=function(pmat)
  local r,rF,c,pmatF;
  pmatF:=[];
  for r in pmat do
    rF:=[];
    for c in r do
      if c=0 then
        Append(rF,[0*Z(Size(F))]);
      else
        Append(rF,[Z(Size(F))^0]);
      fi;
    od;
    Append(pmatF,[rF]);
  od;
end;


PermSub:=function(MG,F)

end;
