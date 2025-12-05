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

@WebServlet("/cambia-gestore")
public class CambiaGestore extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        OrdineDAO ordineDAO = new OrdineDAO();
        Ordine ordine = ordineDAO.doRetrieveById(request.getParameter("ordineID"));

        ordine.setMatricola(request.getParameter("matricola"));
        ordineDAO.updateOrdineMatricola(ordine);
        request.setAttribute("utenteScelto", request.getParameter("utenteScelto"));

        RequestDispatcher dispatcher = request.getRequestDispatcher("gestisci-ordiniByUtente");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso gestisci-ordiniByUtente", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso gestisci-ordiniByUtente", e);
        }
    }
}
