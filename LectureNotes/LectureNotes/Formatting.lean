/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
-/

import VersoManual

set_option autoImplicit false
set_option pp.rawOnError true

open Verso.Genre Manual

section

open Verso Doc Output Html Concrete ToHtml Elab Monad ArgParse Lean.Quote

inductive Decl
  | theorem
  | lemma
  | proposition
  | axiom
  | definition
  deriving Lean.Quote, Lean.ToJson, Lean.FromJson

instance : ToString Decl where
  toString
  | .theorem => "theorem"
  | .lemma => "lemma"
  | .proposition => "proposition"
  | .axiom => "axiom"
  | .definition => "definition"

def thmNumDomain := `Manual.thmNum
def thmRefDomain := `Manual.thmRef

def getNumber? : Lean.Json → Option (Nat × Decl)
  | .arr #[(n : Nat), s] => do
    let d : Decl ← (Lean.fromJson? s).toOption
    return (n, d)
  | _ => none

-- currently all decls must have an internal name for referencing
-- TODO: make this optional
-- TODO: add optional reader-facing titles for each decl
block_extension Block.theorem (decl : Decl) (name : Option String) (title : Option String) where
  data := .arr #[Lean.toJson decl, .str (name.getD ""), .str (title.getD "")]
  traverse id data _ := do
    let .arr #[d, .str name, _] := data
      | logError s!"couldn't deserialize name info from {data}"; return none
    let .ok (decl : Decl) := Lean.fromJson? d
      | logError s!"couldn't deserialize decl info from {data}"; return none
    let path ← (·.path) <$> read
    let tg ← externalTag id path name
    if ((← get).getDomainObject? thmNumDomain (toString id)).isSome then return none
    modify fun s => s.saveDomainObject thmNumDomain (toString id) id
    let obj := (((← get).domains.find? thmNumDomain).getD {}).objects
    let num : Nat := obj.foldl (init := 0) fun i _ o ↦ max i
      (match Lean.Json.getNat? o.data with
        | .ok n => n
        | .error _ => 0)
    modify
      fun s => s.saveDomainObjectData thmNumDomain (toString id) (num + 1 : Nat)
    if name != "" then
      modify fun s => s.saveDomainObject thmRefDomain name id
      modify fun s => s.saveDomainObjectData thmRefDomain name <|
        .arr #[(num + 1 : Nat), Lean.toJson decl]
    return none
  toTeX := none -- this means theorems get lost in latex output
  toHtml :=
    some fun _ goB id data content ↦ do
      let .arr #[decl, .str name, .str title] := data
        | HtmlT.logError s!"couldn't deserialize name info from {data}"; return .empty
      let .ok (decl : Decl) := Lean.fromJson? decl
        | HtmlT.logError s!"couldn't deserialize decl info from {data}"; return .empty
      let some dest := (← read).traverseState.getDomainObject? thmNumDomain (toString id)
        | HtmlT.logError s!"couldn't find theorem reference {name}"; return .empty
      let .ok num := Lean.Json.getNat? dest.data
        | HtmlT.logError s!"couldn't make theorem number"; return .empty
      let nm := (toString decl).capitalize ++ " " ++ toString num
      let nm := if title = "" then nm else nm ++ s!" ({title})"
      if name = "" then
        pure {{
          <div class={{("decl " ++ toString decl)}}>
            <div class="title"><p>{{nm}}</p></div>
            <div class="statement"><p>{{ ← content.mapM goB }}</p></div>
          </div>
          }}
      else
        let some tg := (← read).traverseState.externalTags[id]?
          | HtmlT.logError s!"couldn't find external tag for id {id}"; return .empty
        pure {{
          <div class={{("decl " ++ toString decl)}} id={{tg.htmlId.toString}}>
            <div class="title"><p>{{nm}}</p></div>
            <div class="statement"><p>{{ ← content.mapM goB }}</p></div>
          </div>
          }}
  extraCss := [
    "
div.decl {
  background-color: #f9f9f9;
  padding: 0 1em;
  border: 1px solid;
  border-radius: 5px;
}

div.decl.axiom {
  background-color:#fcfbdc;
}

div.decl .title {
  font-weight: bold;
}

div.decl .statement {
  font-style: italic;
}"
  ]

structure DeclConfig where
  name : Option String := none
  title : Option String := none

open Lean in
def DeclConfig.parse {m} [Monad m] [MonadError m] : ArgParse m DeclConfig :=
  DeclConfig.mk <$>
    optional (.positional `theoremName .string) <*>
    .named `title .string true

open Lean in
instance {m} [Monad m] [MonadError m] : FromArgs DeclConfig m where
  fromArgs := DeclConfig.parse

def decl (d : Decl) : DirectiveExpanderOf DeclConfig
  | cfg, contents => do
    let ⟨name, title⟩ := cfg
    let contents ← contents.mapM elabBlock
    ``(Block.other (Block.theorem $(quote d) $(quote name) $(quote title)) #[ $[ $contents ],* ])

@[directive «theorem»]
def «theorem» : DirectiveExpanderOf DeclConfig := decl .theorem

@[directive «lemma»]
def «lemma» : DirectiveExpanderOf DeclConfig := decl .lemma

@[directive proposition]
def proposition : DirectiveExpanderOf DeclConfig := decl .proposition

@[directive «axiom»]
def «axiom» : DirectiveExpanderOf DeclConfig := decl .axiom

@[directive definition]
def definition : DirectiveExpanderOf DeclConfig := decl .definition

inline_extension Inline.theoremref (name : String) where
  data := .str name
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    some fun goI goB data content ↦ do
      let .str name := data
        | HtmlT.logError s!"(ref) couldn't deserialize name info from {data}"; return .empty
      if name = "" then
        HtmlT.logError "(ref) theoremref requires a nonempty theorem name"; return .empty
      let some dest := (← read).traverseState.getDomainObject? thmRefDomain name
        | HtmlT.logError s!"(ref) couldn't find theorem reference {name}"; return .empty
      let some (num, decl) := getNumber? dest.data
        | HtmlT.logError s!"(ref) couldn't make theorem number"; return .empty
      let id :: _ := dest.ids.toList
        | HtmlT.logError s!"(ref) couldn't find references to theorem {name} in dest"; return .empty
      let some tg := (← read).traverseState.externalTags[id]?
        | HtmlT.logError s!"(ref) couldn't find external tag for id {id}"; return .empty
      let url := tg.link
      let nm := (toString decl).capitalize ++ " " ++ toString num
      return {{ <a href={{url}}>{{nm}}</a> }}

@[role_expander «theoremref»]
def theoremref : RoleExpander
  | args, contents => do
    let title ← ArgParse.run (.positional `theoremName .string) args
    let contents ← contents.mapM elabInline
    let val ← ``(Inline.other (Inline.theoremref $(quote title)) #[ $[ $contents ],* ])
    return #[val]

block_extension Block.proof where
  traverse id data _ := return none
  toTeX := none -- this means proofs get lost in latex output
  toHtml :=
    some fun _ goB id data content ↦ do
      pure {{
        <div class="proof">
          <div class="title"><p>"Proof"</p></div>
          <div><p>{{ ← content.mapM goB }}</p></div>
        </div>
        }}
  extraCss := [
    "
div.proof {
  background-color: #efebff;
  padding: 0 1em;
  border: 1px solid;
  border-radius: 5px;
  margin: 0 0 1em 0;
}

div.proof .title {
  font-weight: bold;
}
"
  ]

@[directive_expander «proof»]
def «proof» : DirectiveExpander
  | _, contents => do
    let contents ← contents.mapM elabBlock
    let val ← ``(Block.other Block.proof #[ $[ $contents ],* ])
    return #[val]

end
