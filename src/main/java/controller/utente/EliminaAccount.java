package controller.utente;

import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;

import java.io.IOException;

@WebServlet("/elimina-account")
public class EliminaAccount extends HttpServlet {
    private UtenteDAO utenteDAO;

    // Permette ai test di iniettare un mock di UtenteDAO
    public void setUtenteDAO(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        // usa l'istanza iniettata per i test o crea una nuova istanza di default
        UtenteDAO dao = this.utenteDAO != null ? this.utenteDAO : new UtenteDAO();
        dao.deleteUtente(utente.getEmail());

        session.invalidate();
        response.sendRedirect("index.html");
    }
}
