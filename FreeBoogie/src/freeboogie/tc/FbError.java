package freeboogie.tc;

import java.util.*;

import com.google.common.collect.Lists;
import genericutils.Err;

import freeboogie.ast.Ast;

/**
  Represents an error.
 
  Various analyzes of the AST produce lists of errors. Each
  error has a type, points to an AST node, and contains
  additional information used to build up an error message
  when {@code toString()} is called.

  TODO(radugrigore): rename this to FbProblem
 
  @author rgrig
 */
public class FbError {
  /** Types of errors. See {@code FbError.toString()} for a description
      of the format. */
  public static enum Type {
    ALREADY_DEF("Variable % already defined"),
    BAD_BREAK_TARGET("Illegal break."),
    BAD_TYPE("Unrelated types: %0 and %1."),
    BV_REQUIRED("Only an integer of fixed width may appear here."),
    DEP_IMPL_SIG("Dependent type in implementation signature."),
    EXACT_TYPE("Type should be %1. (See %0.)"),
    GB_ALREADY_DEF("Identifier % was already defined."),
    GEN_TOOMANY("Too many explicit generics."),
    IP_CNT_MISMATCH("Implementation-Procedure parameter count mismatch."),
    LE("Condition %0 <= %1 not met."),
    MISSING_BLOCK("Inexistent label %."),
    REPEATED_LABEL("Label '%0' appears multiple times in '%1'."),
    NEED_ARRAY("Must be a map."),
    PROC_MISSING("Implementation without procedure."),
    REQ_SPECIALIZATION("Explicit specialization required for %0 at %1."),
    TOO_FAT("The width of this integer (%) is too big."),
    TV_ALREADY_DEF("Type variable % already defined."),
    TYPE_ARGS_MISMATCH("There are %0 arguments instead of %2. See %1."),
    TYPE_CYCLE("Cyclic type synonyms."),
    UNDECL_ID("Undeclared identifier %."),
    UNREACHABLE("Command is unreachable. %");

    private final String templ;
    public String templ() { return templ; }
    Type(String templ) { this.templ = templ; }
  }

  private final Type type;
  private final Ast ast;
  private final Object[] data;

  /**
   * Constructs an error of type {@code type} that refers to
   * the ast node {@code ast} and carries the additional data
   * {@code data}. Note that the content of {@code data} is
   * not checked.
   */
  public FbError(Type type, Ast ast, Object... data) {
    assert type != null;
    assert ast != null;
    this.type = type;
    this.ast = ast;
    this.data = data;
  }

  /** Returns the type of this error. */
  public Type type() { return type; }

  /** Returns the primary AST node associated with this error. */
  public Ast place() { return ast; }

  /** Allows users to explicitely read the attached data. */
  public Object data(int idx) { return data[idx]; }

  /**
   * Constructs a message from the template and the data.
   * The template can contain "%3" to print the fourth data.
   * You can use "%%" to print "%". A single "%" not followed
   * by a number is equivalent to "%0".
   *
   * It may fail with a out-of-bounds exception if not enough
   * data was provided when the error was created.
   */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(ast.loc());
    sb.append(": ");
    int n = type.templ().length();
    for (int i = 0; i < n; ++i) {
      char c = type.templ().charAt(i);
      if (c != '%') sb.append(c);
      else if (i+1 < n && type.templ().charAt(i+1) == '%') {
        ++i; sb.append('%');
      } else {
        int idx = 0;
        while (i+1 < n && Character.isDigit(c = type.templ().charAt(i+1))) {
          idx = 10 * idx + c - '0';
          ++i;
        }
        try {
          sb.append(data[idx].toString());
        } catch (Exception e) {
          Err.error(e.toString());
          Err.internal("INTERNAL ERROR: idx="+idx + " err_type="+type);
        }
      }
    }
    return sb.toString();
  }

  public static boolean reportAll(List<FbError> es) {
    List<FbError> errors = Lists.newArrayList(es);
    Collections.sort(errors, new Comparator<FbError>(){
      @Override public int compare(FbError a, FbError b) {
        return a.ast.loc().compareTo(b.ast.loc());
      }
    });
    for (FbError e : errors) Err.error(e.toString());
    return !es.isEmpty();
  }
}
