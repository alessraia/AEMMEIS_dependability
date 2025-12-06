package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;

import java.io.IOException;

@WebServlet("/modifica-password")
public class ModificaPasswordServlet extends HttpServlet {
    private UtenteDAO utenteDAO;

    // Permette ai test di iniettare un mock di UtenteDAO
    public void setUtenteDAO(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String password = request.getParameter("password");
        String address = null;
        if (password == null || password.isEmpty() || password.length() > 16) {
            address = "/WEB-INF/errorJsp/erroreForm.jsp";
           // response.sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }else {
            address = "area-personale";

            UtenteDAO serviceUtente = this.utenteDAO != null ? this.utenteDAO : new UtenteDAO();
            Utente utente = (Utente) request.getSession().getAttribute("utente");
            utente.setCodiceSicurezza(password);
            serviceUtente.updateUtentePassword(utente);
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            this.doGet(req, resp);
        } catch (ServletException | IOException e) {
            log("Errore durante la gestione POST (doGet)", e);
        }
    }
}
