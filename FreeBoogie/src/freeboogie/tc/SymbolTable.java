package freeboogie.tc;

import freeboogie.ast.*;

/**
 * A structure whose members connect usages to definitions.
 *
 * @author rgrig
 */
public class SymbolTable {
  /** User defined types. */
  public UsageToDefMap<UserType, TypeDecl> types
    = new UsageToDefMap<UserType, TypeDecl>();

  /** Procedures. */
  public UsageToDefMap<CallCmd, Procedure> procs
    = new UsageToDefMap<CallCmd, Procedure>();

  /** Functions. */
  public UsageToDefMap<FunctionApp, FunctionDecl> funcs
    = new UsageToDefMap<FunctionApp, FunctionDecl>();

  /** Identifiers. */
  public UsageToDefMap<Identifier, IdDecl> ids
    = new UsageToDefMap<Identifier, IdDecl>();

  /** Type variables. */
  public UsageToDefMap<UserType, Identifier> typeVars
    = new UsageToDefMap<UserType, Identifier>();
}
