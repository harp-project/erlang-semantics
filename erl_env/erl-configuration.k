requires "erl-syntax.k"

module ERL-CONFIGURATION

  imports ERL-SYNTAX
  imports MAP

  configuration <cfg color="yellow">
                  <k color="green"> $PGM:Pgm ~> $NAME </k>
                  <env color="red"> .Map </env>
                  <funVars> .Map </funVars>
                  <funEnv> .Map </funEnv>
                  <sideEffects> .List </sideEffects>
                  <currentMod> main </currentMod> 
                  <funnames> .Set </funnames>
                  <mods>
                      <mod multiplicity="*" type="Set">
                              <modname> .K </modname>
                              <fundefs color="blue"> .Map </fundefs>
                              <exports> .Set </exports>
                              <imports> .Set </imports>
                      </mod>
                  </mods>
                </cfg>
endmodule