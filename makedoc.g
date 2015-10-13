LoadPackage( "AutoDoc" );

AutoDoc( "itap" : scaffold := true );

PrintTo( "VERSION", PackageInfo( "itap" )[1].Version );

QUIT;
