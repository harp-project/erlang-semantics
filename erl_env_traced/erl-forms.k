requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-FORMS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  rule <k> M1:Module M2:Modules => M1 ~> M2 ... </k> [structural]

  rule <k> M:ModuleAttrib A:Attribs F:FunDefs => M ~> A ~> F ... </k> [structural]
  rule <k> A:Attrib As:Attribs => A ~> As ... </k> [structural]
  rule <k> F1:FunCl F2:FunDefs => F1 ~> F2 ... </k> [structural]

  rule .Attribs ~> F:FunDefs => F:FunDefs [structural]

  // Creates a new module
  rule <k> -module(ModName:Atom). => . ... </k>
       <currentMod> _ => ModName </currentMod>
       <mods> ...
         (. => <mod>
           <modname> ModName </modname>
           <exports> .Set </exports>
           <imports> .Set </imports>
           <fundefs> .Map </fundefs>
         </mod>) ...
       </mods>
    [structural]

  // Insert exports
  rule <k> -export([FAs:NameArities]). => . ... </k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <modname> ModName </modname>
           <exports> OldFAs => OldFAs toFATupleSet(FAs) </exports>
           ...
         </mod> ...
       </mods>
     [structural]

  // Insert imports
  rule <k> -import(M:Atom, [FAs:NameArities]). => . ... </k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <modname> ModName </modname>
           <imports> OldMFAs => OldMFAs toMFATupleSet(M, FAs) </imports>
           ...
         </mod> ...
       </mods>
    [structural]

  // Processing function definitions

  rule <k>Name:Atom(Args) -> Body . =>. ...</k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <fundefs>Rho:Map (.Map => {Name,arity(Args)} |-> ListItem(({Args} -> begin Body end):Match0)) </fundefs>
           ...
         </mod> ...
       </mods> requires notBool {Name,arity(Args)} in keys(Rho)
     [structural]

  rule <k>Name:Atom(Args) -> Body ; =>. ...</k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <fundefs>Rho:Map (.Map => {Name,arity(Args)} |-> ListItem(({Args} -> begin Body end):Match0)) </fundefs>
           ...
         </mod> ...
       </mods> requires notBool {Name,arity(Args)} in keys(Rho)
     [structural]

  rule <k>Name:Atom(Args) -> Body . =>. ...</k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <fundefs>... {Name,arity(Args)} |-> (Bodies =>
                               Bodies ListItem(({Args} -> begin Body end):Match0)) ...</fundefs>
           ...
         </mod> ...
       </mods>
     [structural]

  rule <k>Name:Atom(Args) -> Body ; =>. ...</k>
       <currentMod> ModName </currentMod>
       <mods> ...
         <mod>
           ...
           <fundefs>... {Name,arity(Args)} |-> (Bodies =>
                               Bodies ListItem(({Args} -> begin Body end):Match0)) ...</fundefs>
           ...
         </mod> ...
       </mods>
     [structural]

  // Helper functions

  syntax Set ::= toFATupleSet(NameArities) [function]
  rule toFATupleSet(F:Atom/A:Int) => SetItem({F,A})
  rule toFATupleSet(F:Atom/A:Int, FAs) => SetItem({F,A}) toFATupleSet(FAs)

  syntax Set ::= toMFATupleSet(Atom, NameArities) [function]
  rule toMFATupleSet(M, F:Atom/A:Int) => SetItem({M,F,A})
  rule toMFATupleSet(M, (F:Atom/A:Int, FAs)) => SetItem({M,F,A}) toMFATupleSet(M, FAs)

  syntax Int ::= arity(Exps) [function]
  rule arity(Es) => %count(Es)

endmodule
