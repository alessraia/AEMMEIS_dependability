package model.ordineService;

import model.ConPool;
import model.libroService.Libro;
import model.utenteService.Utente;

import java.sql.*;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class OrdineDAO {

    private RigaOrdineDAO rigaOrdineDAO;

    public OrdineDAO() {
        this(new RigaOrdineDAO());
    }

    public OrdineDAO(RigaOrdineDAO rigaOrdineDAO) {
        this.rigaOrdineDAO = rigaOrdineDAO;
    }

    /*@ public behavior
      @   requires ordine != null;
      @   requires ordine.getIdOrdine() != null && ordine.getIdOrdine().length() > 0;
      @   requires ordine.getCosto() >= 0.0;
      @   requires ordine.getPuntiOttenuti() >= 0;
      @   requires ordine.getPuntiSpesi() >= 0;
      @   requires ordine.getDataEffettuazione() != null;
      @   requires ordine.getEmail() != null && ordine.getEmail().length() > 0;
      @   requires ordine.getStato() != null && ordine.getStato().length() > 0;
      @   requires ordine.getCitta() != null && ordine.getCitta().length() > 0;
      @   requires ordine.getMatricola() != null && ordine.getMatricola().length() > 0;
      @   requires ordine.getRigheOrdine() != null;
      @   assignable \nothing;
      @   ensures true;
      @   signals (RuntimeException e) true;
      @*/
    public void doSave(Ordine ordine){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Ordine (idOrdine, costo, indirizzoSpedizione, citta, puntiOttenuti, puntiSpesi, dataEffettuazione, stato,matricola, email) VALUES(?,?,?,?,?,?,?,?,?,?)");
            ps.setString(1, ordine.getIdOrdine());
            ps.setDouble(2, ordine.getCosto());
            ps.setString(3, ordine.getIndirizzoSpedizione());
            ps.setString(4, ordine.getCitta());
            ps.setInt(5, ordine.getPuntiOttenuti());
            ps.setInt(6, ordine.getPuntiSpesi());
            ps.setDate(7, java.sql.Date.valueOf(ordine.getDataEffettuazione()));
            ps.setString(8, ordine.getStato());
            ps.setString(9, ordine.getMatricola());
            ps.setString(10, ordine.getEmail());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        //aggiunto questo
        for(RigaOrdine riga: ordine.getRigheOrdine()){
            rigaOrdineDAO.doSave(riga);
        }
    }

    /*@ public behavior
      @   requires idOrdine != null && idOrdine.length() > 0;
      @   assignable \nothing;
      @   ensures \result == null || (\result.getIdOrdine() != null && \result.getIdOrdine().equals(idOrdine) && \result.getRigheOrdine() != null);
      @   signals (RuntimeException e) true;
      @*/
    public Ordine doRetrieveById(String idOrdine) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Ordine WHERE idOrdine=?");
            ps.setString(1, idOrdine);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Ordine p = new Ordine();
                //aggiunto questo
                p.setIdOrdine(rs.getString(1));
                p.setCosto(rs.getDouble(2));
                p.setIndirizzoSpedizione(rs.getString(3));
                p.setCitta(rs.getString(4));
                p.setPuntiOttenuti(rs.getInt(5));
                p.setPuntiSpesi(rs.getInt(6));
                Date dataArrivoSQL = rs.getDate(7);
                if (dataArrivoSQL != null) {
                    LocalDate dataArrivo = dataArrivoSQL.toLocalDate();
                    p.setDataArrivo(dataArrivo);
                } else {
                    // Gestione del caso in cui il valore sia null
                    // Ad esempio, assegnare un valore predefinito o fare qualcos'altro
                    p.setDataArrivo(null); // oppure assegna un valore predefinito
                }
                p.setDataEffettuazione(rs.getDate(8).toLocalDate());
                p.setStato(rs.getString(9));
                p.setMatricola(rs.getString(10));
                p.setEmail(rs.getString(11));
                //aggiunto questo
                p.setRigheOrdine(rigaOrdineDAO.doRetrivedByOrdine(idOrdine));

                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires email != null && email.length() > 0;
    @   assignable \nothing;
    @   ensures \result != null
    @        && (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    @   signals (RuntimeException e) true;
    @*/
    public List<Ordine> doRetrieveByUtente(String email) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Ordine WHERE email=?");
            ps.setString(1, email);
            List<Ordine> ordini=new ArrayList<Ordine>();
            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                ordini.add(doRetrieveById(rs.getString(1)));
            }
            return ordini;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires ordine != null
    @        && ordine.getIdOrdine() != null && ordine.getIdOrdine().length() > 0
    @        && ordine.getStato() != null
    @        && ordine.getDataArrivo() != null
             && ordine.getDataEffettuazione() != null && !ordine.getDataArrivo().isBefore(ordine.getDataEffettuazione());
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    //modifico stato e data arrivo dell'ordine
    public void updateOrdine(Ordine ordine){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Ordine SET stato = ?, dataArrivo = ? WHERE idOrdine = ?");
            ps.setString(1, ordine.getStato());
            ps.setDate(2, Date.valueOf(ordine.getDataArrivo()));
            ps.setString(3, ordine.getIdOrdine());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires ordine != null
    @        && ordine.getIdOrdine() != null && ordine.getIdOrdine().length() > 0
    @        && ordine.getStato() != null;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    public void updateStato(Ordine ordine){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Ordine SET stato = ? WHERE idOrdine = ?");
            ps.setString(1, ordine.getStato());
            ps.setString(2, ordine.getIdOrdine());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires ordine != null
    @        && ordine.getIdOrdine() != null && ordine.getIdOrdine().length() > 0
    @        && ordine.getMatricola() != null;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    public void updateOrdineMatricola(Ordine ordine){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Ordine SET matricola = ? WHERE idOrdine = ?");
            ps.setString(1, ordine.getMatricola());
            ps.setString(2, ordine.getIdOrdine());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires email != null && email.length() > 0;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    public void deleteOrdiniByEmail(String email){
        List<Ordine> ordini = this.doRetrieveByUtente(email);
        for(Ordine o : ordini ){
            rigaOrdineDAO.deleteRigaOrdineByIdOrdine(o.getIdOrdine());
        }
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Ordine WHERE email=?");
            ps.setString(1, email);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires idOrdine != null && idOrdine.length() > 0;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    //aggiunto questo
    public void deleteOrdine(String idOrdine){
        rigaOrdineDAO.deleteRigaOrdineByIdOrdine(idOrdine);

        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Ordine WHERE idOrdine=?");
            ps.setString(1, idOrdine);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   assignable \nothing;
    @   ensures \result != null
    @        && (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    @   signals (RuntimeException e) true;
    @*/
    public List<String> doRetrivedAllByIdOrdini(){
        List<String> idOrdini = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Ordine");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                idOrdini.add(rs.getString(1));
            }
            return idOrdini;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

}
