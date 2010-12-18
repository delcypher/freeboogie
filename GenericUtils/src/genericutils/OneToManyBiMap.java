package genericutils;

import java.util.Map;
import java.util.Set;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/** 
  Maintains a 1-to-n correspondence with fast lookups both ways. 
  Don't use {@code null}s.
 */
public class OneToManyBiMap<U, V> {
  private Map<U, Set<V>> manyOf = Maps.newHashMap();
  private Map<V, U> oneOf = Maps.newHashMap();

  public static <U, V> OneToManyBiMap<U, V> make() { 
    return new OneToManyBiMap<U, V>();
  }

  @Deprecated public static <U, V> OneToManyBiMap<U, V> mk() { return make(); }

  public void insert(U u, V v) {
    Set<V> vs = manyOf.get(u);
    if (vs == null) {
      vs = Sets.newHashSet();
      manyOf.put(u, vs);
    }
    U ou = oneOf.get(v);
    if (ou != null && ou != u) 
      throw new IllegalStateException("A V may correspond to only one U.");
    vs.add(v);
    oneOf.put(v, u);
  }

  public void insertAll(U u, Iterable<V> vs) {
    for (V v : vs) insert(u, v);
  }

  public Set<V> manyOf(U u) {
    Set<V> vs = manyOf.get(u);
    if (vs == null) return Sets.newHashSet();
    return Sets.newHashSet(vs);
  }

  public V someOf(U u) {
    Set<V> vs = manyOf.get(u);
    if (vs == null) return null;
    assert !vs.isEmpty();
    return vs.iterator().next();
  }

  public U oneOf(V v) {
    return oneOf.get(v);
  }
}
