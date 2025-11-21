package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.ordineService.RigaOrdine;
import model.ordineService.RigaOrdineDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;

@WebServlet("/riepilogo-ordine")
public class RiepilogoOrdine extends HttpServlet {
    private OrdineDAO ordineDAO;

    // Permette ai test di iniettare un mock di OrdineDAO
    public void setOrdineDAO(OrdineDAO ordineDAO) {
        this.ordineDAO = ordineDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
            return;
        }
        String idOrdine = request.getParameter("idOrdine");
        // Usa l'istanza iniettata (per i test) o crea una nuova istanza di default
        OrdineDAO dao = this.ordineDAO != null ? this.ordineDAO : new OrdineDAO();
        Ordine ordine = dao.doRetrieveById(idOrdine);
        session.setAttribute("ordine", ordine);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/areaPservices/riepilogoOrdine.jsp");
        dispatcher.forward(request, response);
    }
}
