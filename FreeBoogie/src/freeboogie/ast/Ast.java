package freeboogie.ast;

import com.google.common.collect.ImmutableList;
import genericutils.Logger;

import static freeboogie.cli.FbCliOptionsInterface.*;

/** 
 * Base class for the AST hierarchy. 
 *
 * The AST classes are designed to be immutable so that multiple
 * versions of the program can be kept around at the same time,
 * while common parts are shared. Common parts within the same
 * version <i>must not be shared</i>: Many processing stages use
 * a reference to identify the place in the program and this
 * wouldn't work with intra-version sharing. The {@code clone}
 * method should help in situations where you'd be tempted to share.
 *
 * @author rgrig
 */
public abstract class Ast implements Cloneable {

  /** The location of this AST node. */
  protected FileLocation location;

  /**
   * Returns the location of this AST node. 
   * @return the location of this AST node.
   */
  public FileLocation loc() {
    return location;
  }

  protected ImmutableList<Ast> children;
  public abstract ImmutableList<Ast> children();
  
  /**
   * Dispatches to {@code e.eval} based on the static type of the node
   * and the dynamic type of {@code e}.
   * @param <R> the type of the result computed by the evaluator
   * @param e the evaluator
   * @return the result computed by the evaluator
   */
  abstract public <R> R eval(Evaluator<R> e);

  /**
   * Returns a clone of this AST.
   */
  abstract public Ast clone();

  /** Used for debugging. */
  public String hash() {
    return String.format("%03x", (hashCode() * -1717986919) >>> 20);
  }
}
