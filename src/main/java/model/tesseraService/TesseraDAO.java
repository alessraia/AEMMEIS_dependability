package model.tesseraService;

import model.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

public class TesseraDAO {


    /*@
      @ public behavior
      @   requires tessera != null;
      @   requires tessera.getNumero() != null && !tessera.getNumero().isEmpty();
      @   requires tessera.getDataCreazione() != null && tessera.getDataScadenza() != null;
      @   requires tessera.getDataScadenza().equals(tessera.getDataCreazione().plusYears(2));
      @   requires tessera.getEmail() != null && !tessera.getEmail().isEmpty();
      @   ensures tessera.getNumero().equals(\old(tessera.getNumero()))
      @        && tessera.getDataCreazione().equals(\old(tessera.getDataCreazione()))
      @        && tessera.getDataScadenza().equals(\old(tessera.getDataScadenza()))
      @        && tessera.getEmail().equals(\old(tessera.getEmail()));
      @   ensures tessera.getPunti() == 50;
      @   signals_only RuntimeException;
    @*/
    public void doSave(Tessera tessera){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO tessera (numero, dataCreazione, dataScadenza, email) VALUES(?,?,?,?)");
            ps.setString(1, tessera.getNumero());
            ps.setDate(2, java.sql.Date.valueOf(tessera.getDataCreazione()));
            ps.setDate(3, java.sql.Date.valueOf(tessera.getDataScadenza()));
            ps.setString(4, tessera.getEmail());

            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }

            tessera.setPunti(this.doRetrieveById(tessera.getNumero()).getPunti());
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
       @ public behavior
       @   requires numero != null && !numero.isEmpty();
       @   assignable \nothing;
       @   signals_only RuntimeException;
     @*/
    public void deleteTessera(String numero){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM tessera WHERE numero=?");
            ps.setString(1, numero);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
      @ public behavior
      @ requires tessera != null;
      @ requires tessera.getNumero() != null && !tessera.getNumero().isEmpty();
      @ requires tessera.getPunti >= 0;
      @ signals_only RunTimeException;
    @*/
    public void updateTessera(Tessera tessera){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE tessera SET punti = ? WHERE numero = ?");
            ps.setInt(1, tessera.getPunti());
            ps.setString(2, tessera.getNumero());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    /*@
      @ public behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures (\forall int i; 0 <= i && i < \result.size();
      @              \result.get(i) != null
      @           && \result.get(i).getNumero() != null
      @           && !\result.get(i).getNumero().isEmpty()
      @           && \result.get(i).getDataCreazione() != null
      @           && \result.get(i).getDataScadenza() != null
      @           && !\result.get(i).getDataScadenza().isBefore(\result.get(i).getDataCreazione())
      @           && \result.get(i).getEmail() != null
      @           && !\result.get(i).getEmail().isEmpty()
      @          );
      @   signals_only RuntimeException;
    @*/
    public List<Tessera> doRetrivedAll(){
        List<Tessera> tessere = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM tessera");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                Tessera p = new Tessera();
                p.setNumero(rs.getString(1));
                p.setDataCreazione(rs.getDate(2).toLocalDate());
                p.setDataScadenza(rs.getDate(3).toLocalDate());
                p.setPunti(rs.getInt(4));
                p.setEmail(rs.getString(5));
                tessere.add(p);
            }
            return tessere;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

     /*@
     @ public behavior
     @ ensures \result != null
     @ assignable \nothing;
     @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null && \result.get(i).size() != 0);
     @ signals_only RuntimeException;
    @*/
    public List<String> doRetrivedAllByNumero(){
        List<String> numeri = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM tessera");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                numeri.add(rs.getString(1));
            }
            return numeri;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

    /*@
      @ public behavior
      @   requires numero != null && !numero.isEmpty();
      @   assignable \nothing;
      @   ensures \result == null
      @        || (
      @             \result.getNumero() != null
      @          && !\result.getNumero().isEmpty()
      @          && \result.getNumero().equals(numero)
      @          && \result.getDataCreazione() != null
      @          && \result.getDataScadenza() != null
      @          && !\result.getDataScadenza().isBefore(\result.getDataCreazione())
      @          && \result.getEmail() != null
      @          && !\result.getEmail().isEmpty()
      @          && \result.getPunti >= 0
      @        );
      @   signals_only RuntimeException;
    @*/
    public Tessera doRetrieveById(String numero) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM tessera WHERE numero=?");
            ps.setString(1, numero);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Tessera p = new Tessera();
                p.setNumero(rs.getString(1));
                p.setDataCreazione(rs.getDate(2).toLocalDate());
                p.setDataScadenza(rs.getDate(3).toLocalDate());
                p.setPunti(rs.getInt(4));
                p.setEmail(rs.getString(5));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
      @ public behavior
      @   requires email != null && !email.isEmpty();
      @   assignable \nothing;
      @   ensures \result == null
      @        || (
      @             \result.getEmail() != null
      @          && !\result.getEmail().isEmpty()
      @          && \result.getEmail().equals(email)
      @          && \result.getDataCreazione() != null
      @          && \result.getDataScadenza() != null
      @          && !\result.getDataScadenza().isBefore(\result.getDataCreazione())
      @          && \result.getNumero() != null
      @          && !\result.getNumero().isEmpty()
      @          && \result.getPunti >= 0
      @        );
      @   signals_only RuntimeException;
    @*/
    public Tessera doRetrieveByEmail(String email) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM tessera WHERE email=?");
            ps.setString(1, email);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Tessera p = new Tessera();
                p.setNumero(rs.getString(1));
                p.setDataCreazione(rs.getDate(2).toLocalDate());
                p.setDataScadenza(rs.getDate(3).toLocalDate());
                p.setPunti(rs.getInt(4));
                p.setEmail(rs.getString(5));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }
}
