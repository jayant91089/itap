#############################################################################
##
##                                                            itap package
##
##  Copyright 2013,           Jayant Apte,
##                                  John Walsh,         Drexel University
##
#############################################################################
if TestPackageAvailability("fining")=fail then
  ReadPackage( "itap", "gap/itap_light.gi" );
else
  ReadPackage("itap", "gap/itap.gi");
fi;
