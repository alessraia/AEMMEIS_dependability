package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;

@WebServlet("/visualizza-ordini")
public class VisualizzaOrdini extends HttpServlet {
    private OrdineDAO ordineDAO;

    // Permette ai test di iniettare un mock di OrdineDAO
    public void setOrdineDAO(OrdineDAO ordineDAO) {
        this.ordineDAO = ordineDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        //metto gli ordini dell'utente in sessione così da poter
        //gestire meglio la stampa
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
            return;
        }
        // Usa l'istanza iniettata (per i test) o crea una nuova istanza di default
        OrdineDAO dao = this.ordineDAO != null ? this.ordineDAO : new OrdineDAO();
        List<Ordine> ordini = dao.doRetrieveByUtente(utente.getEmail());
        session.setAttribute("ordini", ordini);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/areaPservices/visualizzaOrdini.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }
}
