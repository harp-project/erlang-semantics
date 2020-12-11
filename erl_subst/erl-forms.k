requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-FORMS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  rule M1:Module M2:Modules => M1 ~> M2 [structural]

  rule M:ModuleAttrib A:Attribs F:FunDefs => M ~> A ~> F [structural]
  rule A:Attrib As:Attribs => A ~> As [structural]
  rule F1:FunCl F2:FunDefs => F1 ~> F2 [structural]

  rule .Attribs ~> F:FunDefs => F:FunDefs [structural]

  // Creates a new module
  rule <k> -module(ModName:Atom). => . ... </k>
       <currentmod> _ => ModName </currentmod>
       <mods> ...
         (. => <mod>
           <modName> ModName </modName>
           <exports> .Set </exports>
           <imports> .Set </imports>
           <defs> .Map </defs>
         </mod>) ...
       </mods>
    [structural]

  // Insert exports
  rule <k> -export([FAs:NameArities]). => . ... </k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <modName> ModName </modName>
           <exports> OldFAs => OldFAs toFATupleSet(FAs) </exports>
           ...
         </mod> ...
       </mods>
     [structural]

  // Insert imports
  rule <k> -import(M:Atom, [FAs:NameArities]). => . ... </k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <modName> ModName </modName>
           <imports> OldMFAs => OldMFAs toMFATupleSet(M, FAs) </imports>
           ...
         </mod> ...
       </mods>
    [structural]

  // Processing function definitions

  rule <k>Name:Atom(Args) -> Body . =>. ...</k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <defs>Rho:Map (.Map => {Name,arity(Args)} |-> ListItem(({Args} -> Body):Match0)) </defs>
           ...
         </mod> ...
       </mods> requires notBool {Name,arity(Args)} in keys(Rho)
     [structural]

  rule <k>Name:Atom(Args) -> Body ; =>. ...</k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <defs>Rho:Map (.Map => {Name,arity(Args)} |-> ListItem(({Args} -> Body):Match0)) </defs>
           ...
         </mod> ...
       </mods> requires notBool {Name,arity(Args)} in keys(Rho)
     [structural]

  rule <k>Name:Atom(Args) -> Body . =>. ...</k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <defs>... {Name,arity(Args)} |-> (Bodies =>
                               Bodies ListItem(({Args} -> Body):Match0)) ...</defs>
           ...
         </mod> ...
       </mods>
     [structural]

  rule <k>Name:Atom(Args) -> Body ; =>. ...</k>
       <currentmod> ModName </currentmod>
       <mods> ...
         <mod>
           ...
           <defs>... {Name,arity(Args)} |-> (Bodies =>
                               Bodies ListItem(({Args} -> Body):Match0)) ...</defs>
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
  rule arity(Es) => count(Es)

endmodule