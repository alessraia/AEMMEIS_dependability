package model.wishList;

import model.libroService.Libro;

import java.util.ArrayList;
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
    //@ pure
    public String getEmail() {
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
    //@ pure
    public List<Libro> getLibri() {
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
      @   requires libro != null;
      @   ensures this.libri != null;
      @   ensures this.libri.contains(libro);
      @*/
    public void addLibro(Libro libro){
        if (libri == null) {
            libri = new ArrayList<Libro>();
        }
        libri.add(libro);
    }
}
