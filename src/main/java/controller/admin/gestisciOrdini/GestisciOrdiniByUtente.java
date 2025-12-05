package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/gestisci-ordiniByUtente")
public class GestisciOrdiniByUtente extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        OrdineDAO ordineDAO = new OrdineDAO();
        UtenteDAO utenteDAO = new UtenteDAO();
        Utente utente = utenteDAO.doRetrieveById(request.getParameter("utenteScelto"));
        List<Ordine> ordini = ordineDAO.doRetrieveByUtente(utente.getEmail());

        request.setAttribute("utenteScelto", utente);
        request.setAttribute("ordiniUtente", ordini);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/ordini/stampaOrdini.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/admin/ordini/stampaOrdini.jsp", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/admin/ordini/stampaOrdini.jsp", e);
        }
    }
}
