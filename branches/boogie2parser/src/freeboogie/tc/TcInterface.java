package freeboogie.tc;

import java.util.*;

import genericutils.SimpleGraph;

import freeboogie.ErrorsFoundException;
import freeboogie.ast.*;

/**
 * Interface for type-checkers.
 *
 * Users call {@code process} on an AST and they get back a
 * list of type errors. Additional information can be queried
 * using the other methods. Note in particular the method {@code
 * getAST()}: It is possible for an implementation to modify the
 * AST, and in that case all the provided information referrs to
 * the modified AST.
 *
 * This behaves as a Facade for the package.
 *
 * @author rgrig
 */
public interface TcInterface {
  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return the detected errors 
   */
  List<FbError> process(Program p);

  /**
   * Returns the flow graph of {@code bdy}.
   * @param bdy the body whose flow graph is requested
   * @return the flow graph of {@code bdy}
   */
  SimpleGraph<Command> flowGraph(Body bdy);
  
  /**
   * Returns the map of expressions to types.
   * @return the map of expressions to types.
   */
  Map<Expr, Type> types();

  /**
   * Returns the map from implementations to procedures.
   * @return the map from implementations to procedures
   */
  UsageToDefMap<Implementation, Procedure> implProc();

  /**
   * Returns the map from implementation parameters to procedure parameters.
   * @return the map from implementation parameters to procedure parameters
   */
  UsageToDefMap<VariableDecl, VariableDecl> paramMap();

  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  SymbolTable st(); 

  /**
   * Returns the (possibly modified) AST that was last processed.
   * @return the last processed AST
   */
  Program ast();
  
}
