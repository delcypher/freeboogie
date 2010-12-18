package freeboogie.tc;

import java.util.*;

import genericutils.SimpleGraph;

import freeboogie.ast.*;

/**
  Interface for type-checkers.
 
  Users call {@code process} on an AST and they get back a
  list of type errors. Additional information can be queried
  using the other methods. Note in particular the method {@code
  getAST()}: It is possible for an implementation to modify the
  AST, and in that case all the provided information refers to
  the modified AST.
 
  This behaves as a Facade for the package.

  TODO(radugrigore): this should be removed in the favor of 
      DecoratedProgramInterface
 
  @author rgrig
 */
public interface TcInterface {
  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return the detected errors 
   */
  Program process(Program p) throws ErrorsFoundException;

  /**
   * Returns the flow graph of {@code bdy}.
   * @param bdy the body whose flow graph is requested
   * @return the flow graph of {@code bdy}
   */
  SimpleGraph<Command> flowGraph(Implementation implementation);

  /** Returns an object that can link commands to labels.
      @see LabelsCollector */
  LabelsCollector labels();
  
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
}

