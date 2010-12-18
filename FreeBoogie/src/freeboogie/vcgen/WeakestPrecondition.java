package freeboogie.vcgen;

import java.util.ArrayList;

import com.google.common.collect.ImmutableList;

import freeboogie.ast.Command;
import freeboogie.ast.Body;
import freeboogie.backend.Term;
import freeboogie.tc.TcInterface;

/**
 * Computes weakest precondition for one {@code
 * Implementation}.
 *
 * @author J. Charles (julien.charles@gmail.fr)
 * @author rgrig
 * @param <T> the type of the terms
 */
public class WeakestPrecondition<T extends Term<T>> extends StrongestPostcondition<T> {
  private T pre(Command b) {
    T r = preCache.get(b);
    if (r != null) return r;
    
    r = post(b);
    if (isAssert(b)) {
      if (assumeAsserts) {
       r = term.mk("and", term(b), term.mk("implies", term(b), r));
      } else {
        r = term.mk("and", term(b), r);
      }
    } else if (isAssume(b)) {
      r = term.mk("implies", term(b), r);
    }      
    
    preCache.put(b, r);
    return r;
  }

  private T post(Command b) {
    T r = postCache.get(b);
    if (r != null) return r;
    ImmutableList.Builder<T> fromAnd = ImmutableList.builder();
    for (Command p : flow.to(b)) 
      fromAnd.add(pre(p));
    r = term.mk("and", fromAnd.build());
    postCache.put(b, r);
    return r;
  }

  @Override
  public T vc() {
    return pre(currentBody().block().commands().get(0));
  }
}
