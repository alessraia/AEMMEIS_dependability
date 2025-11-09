package model.wishList;

import model.libroService.Libro;

import java.util.List;
/*@ nullable_by_default @*/
public class WishList {
    //@ spec_public
    private String email;
    //@ spec_public
    List<Libro> libri;

    /*@ public normal_behavior
      @   ensures \result == email;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getEmail() {
        return email;
    }

    /*@ public normal_behavior
      @   assignable this.email;
      @   ensures this.email == email;
      @*/
    public void setEmail(String email) {
        this.email = email;
    }

    /*@ public normal_behavior
      @   ensures \result == libri;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<Libro> getLibri() {
        return libri;
    }

    /*@ public normal_behavior
      @   requires libri == null
      @        || (\forall int i; 0 <= i && i < libri.size(); libri.get(i) != null);
      @   assignable this.libri;
      @   ensures this.libri == libri;
      @*/
    public void setLibri(List<Libro> libri) {
        this.libri = libri;
    }

    /*@ public normal_behavior
      @   requires libri != null;
      @   requires libro != null;
      @   assignable this.libri.*;
      @   ensures libri.contains(libro);
      @*/
    public void addLibro(Libro libro){
        libri.add(libro);
    }
}
