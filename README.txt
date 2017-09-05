======================================================================
Package Summary
======================================================================

This plugin provides a translator from WyIL high-level bytecode to Boogie.

Setup
=====
1. Compile this plugin using Maven:  
      mvn package
      
2. Copy target/wy2boogie-0.4.jar into the 'lib' directory of your Whiley (wdk) installation.
      cp target/wy2boogie-0.4.jar /home/you/tools/wdk-v0.4.1/lib
      
3. Add the following line to the 'config.wyml' file in your Whiley installation:
      wy2boogie = "wy2boogie.Activator"

Usage
=====
1. Run 'wy boogie <YourProgram>.whiley' to translate your Whiley program to Boogie.
     wy boogie Program.whiley
   
2. Concatenate wval.bpl and Program.bpl and send them to Boogie.  E.g. (in this directory)  
     Boogie wval.bpl Program.bpl

Notes
=====
You can use Boogie online at http://rise4fun.com/Boogie

Or see the following websites for instructions on how to build your own Boogie and Z3:
* https://github.com/boogie-org/boogie
* https://github.com/Z3Prover/z3

