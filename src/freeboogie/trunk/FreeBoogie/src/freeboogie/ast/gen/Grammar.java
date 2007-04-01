/** Public domain. */

package freeboogie.ast.gen;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents an abstract grammag (AG). It is basically a map from
 * class names to {@code AgClass} objects plus a couple of utility
 * methods.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Grammar {

  /**
   * A map from class names to {@code AgClass} objects.
   */
  public Map<String, AgClass> classes;
  
  /** Creates a new grammar object. */
  public Grammar() {
    classes = new HashMap<String, AgClass>(100);
  }
  
  /**
   * Return the class with the specified name, initializing an 
   * {@code AgClass} object if necessary.
   * 
   * @param name the class name
   * @return the {@code AgClass} object representing the class
   */
  public AgClass getAgClass(String name) {
    AgClass cls = classes.get(name);
    if (cls == null) {
      cls = new AgClass();
      classes.put(name, cls);
      cls.name = name;
    }
    return cls;
  }
  
  /**
   * We set here all things that are left behind by {@code AgParser}.
   * 
   * A member is considered to be a primitive iff its type is not a 
   * class name.
   * 
   * If a class does not have an explicit base class it is set 
   * to |defaultBase|.
   * 
   * @param defaultBaseName the default base class name 
   */
  public void makeConsistent(String defaultBaseName) {
    for (AgClass c : classes.values()) {
      if (c.base == null) c.base = defaultBaseName;
      for (AgMember m : c.members) {
        m.primitive = classes.containsKey(m.type);
      }
    }
  }
}
