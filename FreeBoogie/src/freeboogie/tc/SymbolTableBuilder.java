package freeboogie.tc;

import java.util.*;

import com.google.common.collect.ImmutableList;
import genericutils.StackedHashMap;

import freeboogie.ast.*;

/**
  Constructs a {@code SymbolTable} from an AST.

  @author rgrig
  @author miko
 */
@SuppressWarnings("unused") // lots of unused parameters
public class SymbolTableBuilder extends Transformer implements StbInterface {
  private StackedHashMap<String, VariableDecl> localVarDecl;
  private StackedHashMap<String, Identifier> typeVarDecl;

  private SymbolTable symbolTable;
  private GlobalsCollector gc;

  // problems found while building the symbol table
  private List<FbError> errors;

  // for modifies spec we ignore the arguments
  private boolean lookInLocalScopes;

  /**
   * Builds a symbol table. Reports name clashes (because it
   * uses {@code GlobalsCollector}. Reports undeclared variables.
   * @param ast the AST to analyze
   * @return a list with the problems detected
   */
  @Override
  public Program process(Program p, TcInterface typechecker)
  throws ErrorsFoundException {
    typechecker = null; // NOT used later
    localVarDecl = new StackedHashMap<String, VariableDecl>();
    typeVarDecl = new StackedHashMap<String, Identifier>();
    symbolTable = new SymbolTable();
    gc = new GlobalsCollector();
    lookInLocalScopes = true;
    errors = gc.process(p);
    p = (Program) p.eval(this);
    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);
    return p;
  }

  @Override public SymbolTable st() { return symbolTable; }
  @Override public GlobalsCollector gc() { return gc; }

  // === helpers ===

  // reports an error at location l if d is null
  private <T> T check(T d, String s, Ast l) {
    if (d != null) return d;
    errors.add(new FbError(FbError.Type.UNDECL_ID, l, s));
    return null;
  }

  private IdDecl lookupId(String s, Ast l) {
//System.out.println("lookup " + s + " at " + l.loc());
    IdDecl r = localVarDecl.get(s);
    if (r == null) r = gc.idDef(s);
    return check(r, s, l);
  }

  private void collectTypeVars(
      Map<String, Identifier> tv,
      ImmutableList<Identifier> ids
  ) {
    for (Identifier ai : ids) {
      if (tv.get(ai.id()) != null)
        errors.add(new FbError(FbError.Type.TV_ALREADY_DEF, ai, ai.id()));
      symbolTable.typeVars.seenDef(ai);
      typeVarDecl.put(ai.id(), ai);
    }
  }

  // === visit methods ===

  @Override public void see(UserType userType) {
    String name = userType.name();
    Identifier tv = typeVarDecl.get(name);
    if (tv != null)
      symbolTable.typeVars.put(userType, tv);
    else
      symbolTable.types.put(userType, check(gc.typeDef(name), name, userType));
    AstUtils.evalListOfType(userType.typeArgs(), this);
  }

  @Override public void see(MapType mapType) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), mapType.typeVars());
    AstUtils.evalListOfType(mapType.idxTypes(), this);
    mapType.elemType().eval(this);
    typeVarDecl.pop();
  }

  @Override public void see(CallCmd callCmd) {
    String p = callCmd.procedure();
    symbolTable.procs.put(callCmd, check(gc.procDef(p), p, callCmd));
    AstUtils.evalListOfType(callCmd.types(), this);
    AstUtils.evalListOfIdentifier(callCmd.results(), this);
    AstUtils.evalListOfExpr(callCmd.args(), this);
  }

  @Override public void see(FunctionApp atomFun) {
    String f = atomFun.function();
    symbolTable.funcs.put(atomFun, check(gc.funDef(f), f, atomFun));
    AstUtils.evalListOfType(atomFun.types(), this);
    AstUtils.evalListOfExpr(atomFun.args(), this);
  }

  @Override public void see(Identifier atomId) {
    symbolTable.ids.put(atomId, lookupId(atomId.id(), atomId));
    AstUtils.evalListOfType(atomId.types(), this);
  }

  // === collect info from local scopes ===
  @Override public void see(VariableDecl variableDecl) {
    String name = variableDecl.name();
    symbolTable.ids.seenDef(variableDecl);
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), variableDecl.typeArgs());
    Map<String, VariableDecl> scope = localVarDecl.peek();
    if (localVarDecl.frames() > 0 && name != null) {
      // we are in a local scope
      VariableDecl old = scope.get(name);
      if (old != null)
        errors.add(new FbError(FbError.Type.ALREADY_DEF, variableDecl, name));
      else
        scope.put(name, variableDecl);
    }
    variableDecl.type().eval(this);
    typeVarDecl.pop();
  }

  @Override public void see(TypeDecl typeDecl) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), typeDecl.typeArgs());
    if (typeDecl.type() != null) typeDecl.type().eval(this);
    typeVarDecl.pop();
    symbolTable.types.seenDef(typeDecl);
  }

  @Override public void see(ConstDecl constDecl) {
    symbolTable.ids.seenDef(constDecl);
    constDecl.type().eval(this);
  }

  @Override public void see(Signature signature) {
    collectTypeVars(typeVarDecl.peek(), signature.typeArgs());
    AstUtils.evalListOfVariableDecl(signature.args(), this);
    AstUtils.evalListOfVariableDecl(signature.results(), this);
  }


  // === keep track of local scopes ===
  @Override public void see(Procedure procedure) {
    symbolTable.procs.seenDef(procedure);
    localVarDecl.push();
    typeVarDecl.push();
    procedure.sig().eval(this);
    AstUtils.evalListOfPreSpec(procedure.preconditions(), this);
    AstUtils.evalListOfPostSpec(procedure.postconditions(), this);
    AstUtils.evalListOfModifiesSpec(procedure.modifies(), this);
    typeVarDecl.pop();
    localVarDecl.pop();
  }

  @Override public void see(Implementation implementation) {
    localVarDecl.push();
    typeVarDecl.push();
    implementation.sig().eval(this);
    implementation.body().eval(this);
    typeVarDecl.pop();
    localVarDecl.pop();
  }

  @Override public void see(FunctionDecl function) {
    symbolTable.funcs.seenDef(function);
    typeVarDecl.push();
    function.sig().eval(this);
    typeVarDecl.pop();
  }

  @Override public void see(Quantifier atomQuant) {
    localVarDecl.push();
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), atomQuant.typeVariables());
    AstUtils.evalListOfVariableDecl(atomQuant.vars(), this);
    AstUtils.evalListOfAttribute(atomQuant.attributes(), this);
    atomQuant.expression().eval(this);
    typeVarDecl.pop();
    localVarDecl.pop();
  }

  @Override public void see(Axiom axiom) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), axiom.typeArgs());
    axiom.expr().eval(this);
    typeVarDecl.pop();
  }

  @Override public void see(AssertAssumeCmd assertAssumeCmd) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), assertAssumeCmd.typeArgs());
    assertAssumeCmd.expr().eval(this);
    typeVarDecl.pop();
  }

  // === remember if we are below a modifies spec ===

  @Override public void see(ModifiesSpec modifiesSpec) {
    assert lookInLocalScopes : "no nesting of modifies";
    lookInLocalScopes = false;
    AstUtils.evalListOfIdentifier(modifiesSpec.ids(), this);
    lookInLocalScopes = true;
  }

  @Override public void see(PostSpec postSpec) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), postSpec.typeArgs());
    postSpec.expr().eval(this);
    typeVarDecl.pop();
  }

  @Override public void see(PreSpec preSpec) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), preSpec.typeArgs());
    preSpec.expr().eval(this);
    typeVarDecl.pop();
  }
}
