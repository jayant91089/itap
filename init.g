#############################################################################
##
##  init.g                itap package
##                                                          Jayant Apte
##
##  Copyright 2015 Lehrstuhl D für Mathematik, RWTH Aachen
##
##  Reading the declaration part of the itap package.
##
#############################################################################
if TestPackageAvailability("fining")=fail then
  ReadPackage( "itap", "gap/itap_light.gd" );
else
  ReadPackage("itap", "gap/itap.gd");
fi;
