package controller.HomePage;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.ServletRequest;
import jakarta.servlet.ServletResponse;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;

import java.io.IOException;

@WebServlet("/area-personale")
public class AreaPersonaleServlet extends HttpServlet {
    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession(false);
        String address;
        if (session != null && session.getAttribute("utente") != null) {
            address = "/WEB-INF/results/areaPersonale.jsp";
            Utente utente = (Utente) session.getAttribute("utente");
            if(Validator.checkIfUserAdmin(utente))
                address = "/WEB-INF/results/admin/areaPersonaleAdmin.jsp";
        } else {
            address = "/WEB-INF/results/login.jsp";
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/about-us.jsp", e);
            throw e;
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/about-us.jsp", e);
            throw e;
        }
    }

    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
