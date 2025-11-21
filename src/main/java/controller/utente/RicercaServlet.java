package controller.utente;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;
@WebServlet("/ricerca-servlet")
public class RicercaServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
            return;
        }
        String query = request.getParameter("q");
        // allow injection for tests
        LibroDAO libroService = this.getLibroDAO() != null ? this.getLibroDAO() : new LibroDAO();
        String address = null;
        if(query==null){
            address = "/WEB-INF/errorJsp/erroreForm.jsp";
        }
        else if(query.isEmpty()){
            address="index.html";
        }
        else {
            address="/WEB-INF/results/ricerca.jsp";
            List<Libro> results = libroService.Search(query);
            request.setAttribute("results", results);
            request.setAttribute("q", query);
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        dispatcher.forward(request, response);

    }

    // --- Testability: injection getter/setter for LibroDAO ---
    private LibroDAO libroDAO;

    public void setLibroDAO(LibroDAO libroDAO) {
        this.libroDAO = libroDAO;
    }

    public LibroDAO getLibroDAO() {
        return this.libroDAO;
    }
}
