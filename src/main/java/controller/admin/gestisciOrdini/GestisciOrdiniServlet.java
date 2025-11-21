package controller.admin.gestisciOrdini;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/gestisci-ordini")
public class GestisciOrdiniServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        UtenteDAO utenteDAO = new UtenteDAO();
        List<Utente> utenti = utenteDAO.doRetrieveAll();

        for (int i = utenti.size() - 1; i >= 0; i--) {
            if (Validator.checkIfUserAdmin(utenti.get(i))) {
                utenti.remove(i);
            }
        }

        request.setAttribute("utenti", utenti);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/ordini/gestisciOrdini.jsp");
        dispatcher.forward(request, response);
    }
}
