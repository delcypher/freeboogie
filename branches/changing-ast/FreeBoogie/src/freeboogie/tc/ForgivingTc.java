package freeboogie.tc;

import java.util.*;
import java.util.logging.Logger;

import genericutils.SimpleGraph;

import freeboogie.ErrorsFoundException;
import freeboogie.ast.*;

//DBG import java.io.PrintWriter;
//DBG import freeboogie.astutil.*;

/**
 * Typechecks the AST and modifies it a little if that will
 * fix errors. Code generated by Spec# that would otherwise
 * be illegal because certain constructs were modified/deprecated
 * in FreeBoogie should pass if this typechecker is used. The
 * modified AST, which satisfies all the rules of FreeBoogie,
 * can be retrieved.
 *
 * @author rgrig
 */
public class ForgivingTc extends Transformer implements TcInterface {

  private static final Logger log = Logger.getLogger("freeboogie.tc"); 

  private static final EnumSet<FbError.Type> fixable = 
    EnumSet.of(FbError.Type.REQ_SPECIALIZATION);

  // does the real work
  private TypeChecker tc;

  public ForgivingTc() {
    tc = new TypeChecker();
    tc.setAcceptOld(true);
  }

  @Override public Declaration getAST() { return tc.getAST(); }

  @Override public Program process(Program p) throws ErrorsFoundException {
    List<FbError> errors = process(p.ast);
    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);
    return new Program(getAST(), p.fileName);
  }

  @Override
  public List<FbError> process(Declaration ast) {
    boolean unfixable;
    int oldErrCnt = Integer.MAX_VALUE;
    List<FbError> errors, filteredErrors = new ArrayList<FbError>();
    while (true) {
      errors = tc.process(ast);
      ast = tc.getAST();

      /* We stop if one of the following holds:
       * (1) There is an unfixable error.
       * (2) The number of potentially fixable errors did not decrease.
       * (3) There are zero (potentially fixable) errors.
       */
      unfixable = false;
      filteredErrors.clear();
      for (FbError e : errors) {
        if (fixable.contains(e.type()))
          filteredErrors.add(e);
        else
          unfixable = true;
      }
      int errCnt = filteredErrors.size();
      if (unfixable || errCnt == 0 || errCnt >= oldErrCnt) break;
      
      oldErrCnt = errCnt;
      ast = fix(ast, filteredErrors);
      log.info("Running TypeChecker again.");
    }
    return errors;
  }

  @Override
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return tc.getFlowGraph(impl);
  }  
  
  @Override
  public SimpleGraph<Block> getFlowGraph(Body bdy) {
    return tc.getFlowGraph(bdy);
  }
  

  @Override
  public Map<Expr, Type> getTypes() {
    return tc.getTypes();
  }

  @Override
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return tc.getImplProc();
  }

  @Override
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return tc.getParamMap();
  }

  @Override
  public SymbolTable getST() {
    return tc.getST();
  }

  // this guy does most of the work
  private Declaration fix(Declaration ast, List<FbError> errors) {
    Inferrer inferrer = new Inferrer();
    Specializer specializer = new Specializer();

    HashMap<Expr, AtomId> filteredErrors = new HashMap<Expr, AtomId>();
    for (FbError e : errors) {
      switch (e.type()) {
      case REQ_SPECIALIZATION:
        filteredErrors.put((Expr)e.place(), (AtomId)e.data(2));
        break;
      default:
        // do nothing
      }
    }
    inferrer.process(ast, tc.getTypes());
    Map<Expr, Type> desired = inferrer.getGoodTypes();
    ast = specializer.process(
      ast, tc.getST(), filteredErrors, 
      desired, tc.getImplicitSpec());

    /* DBG 
    System.out.println("=== RESULT OF TYPE INFERENCE ===");
    PrintWriter pw = new PrintWriter(System.out);
    PrettyPrinter pp = new PrettyPrinter(pw);
    ast.eval(pp);
    pw.flush();
    */

    return ast;
  }
}
